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
% DateTime   : Thu Dec  3 13:23:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 245 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  495 (1467 expanded)
%              Number of equality atoms :   36 ( 225 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f85,f90,f96,f103,f112,f121,f136,f143,f151,f164])).

fof(f164,plain,
    ( ~ spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f160,f149,f74])).

fof(f74,plain,
    ( spl5_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f149,plain,
    ( spl5_17
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_17 ),
    inference(resolution,[],[f150,f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f150,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( ~ spl5_17
    | ~ spl5_7
    | ~ spl5_11
    | spl5_16 ),
    inference(avatar_split_clause,[],[f144,f140,f94,f74,f149])).

fof(f94,plain,
    ( spl5_11
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f140,plain,
    ( spl5_16
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ spl5_11
    | spl5_16 ),
    inference(resolution,[],[f141,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( ~ spl5_8
    | ~ spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f138,f133,f140,f78])).

fof(f78,plain,
    ( spl5_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f133,plain,
    ( spl5_15
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f138,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_15 ),
    inference(resolution,[],[f134,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f134,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f133])).

fof(f136,plain,
    ( ~ spl5_15
    | ~ spl5_7
    | ~ spl5_10
    | spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f129,f119,f83,f88,f74,f133])).

fof(f88,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f83,plain,
    ( spl5_9
  <=> v2_tops_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f119,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | spl5_9
    | ~ spl5_14 ),
    inference(resolution,[],[f128,f84])).

fof(f84,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f128,plain,
    ( ! [X0] :
        ( v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f124,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f124,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK4(X0,sK2),X0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(sK4(X0,sK2),X0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f120,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(sK4(X0,sK2),X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( ~ spl5_6
    | spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f117,f110,f119,f70])).

fof(f70,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X1,sK0)
        | v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(sK4(X2,sK2),X3)
        | v4_pre_topc(sK4(X2,sK2),X1)
        | ~ m1_subset_1(sK4(X2,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | v2_tops_2(sK2,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X1,sK0)
        | v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_tops_2(sK2,X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl5_8
    | spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f107,f101,f110,f78])).

fof(f101,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_12 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1)))
        | v4_pre_topc(sK4(X0,sK2),X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f104,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f104,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK4(X0,sK2),sK0)
        | ~ m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_2(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( ~ spl5_8
    | ~ spl5_6
    | spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f97,f54,f101,f70,f78])).

fof(f54,plain,
    ( spl5_2
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_tops_2(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,
    ( ~ spl5_7
    | spl5_11
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f91,f62,f94,f74])).

fof(f62,plain,
    ( spl5_4
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f91,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f39,f63])).

fof(f63,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f90,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f86,f66,f58,f88])).

fof(f58,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f67,f59])).

fof(f59,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f85,plain,
    ( ~ spl5_9
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f81,f58,f50,f83])).

fof(f50,plain,
    ( spl5_1
  <=> v2_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( ~ v2_tops_2(sK2,sK1)
    | spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f51,f59])).

fof(f51,plain,
    ( ~ v2_tops_2(sK3,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f80,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X1)
                & v2_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,sK1)
              & v2_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,sK1)
            & v2_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK1)
          & v2_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK1)
        & v2_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v2_tops_2(sK3,sK1)
      & v2_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).

fof(f76,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f35,f58])).

fof(f35,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f54])).

fof(f36,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f50])).

fof(f37,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (18123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (18123)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (18132)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (18131)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f85,f90,f96,f103,f112,f121,f136,f143,f151,f164])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ~spl5_7 | spl5_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f160,f149,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl5_7 <=> l1_pre_topc(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl5_17 <=> m1_pre_topc(sK1,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | spl5_17),
% 0.21/0.47    inference(resolution,[],[f150,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK1) | spl5_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~spl5_17 | ~spl5_7 | ~spl5_11 | spl5_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f144,f140,f94,f74,f149])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl5_11 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl5_16 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK1) | (~spl5_11 | spl5_16)),
% 0.21/0.47    inference(resolution,[],[f141,f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK1)) ) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_16 | spl5_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f138,f133,f140,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl5_8 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl5_15 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | spl5_15),
% 0.21/0.47    inference(resolution,[],[f134,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | spl5_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f133])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~spl5_15 | ~spl5_7 | ~spl5_10 | spl5_9 | ~spl5_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f129,f119,f83,f88,f74,f133])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl5_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl5_9 <=> v2_tops_2(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl5_14 <=> ! [X1,X0] : (v4_pre_topc(sK4(X0,sK2),X1) | ~m1_pre_topc(X1,sK0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK1,sK0) | (spl5_9 | ~spl5_14)),
% 0.21/0.47    inference(resolution,[],[f128,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~v2_tops_2(sK2,sK1) | spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0] : (v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_14),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0] : (v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_14),
% 0.21/0.47    inference(resolution,[],[f124,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(sK4(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(rectify,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (v4_pre_topc(sK4(X0,sK2),X0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl5_14),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v4_pre_topc(sK4(X0,sK2),X0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_14),
% 0.21/0.47    inference(resolution,[],[f120,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,sK0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v4_pre_topc(sK4(X0,sK2),X1)) ) | ~spl5_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~spl5_6 | spl5_14 | ~spl5_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f110,f119,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl5_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl5_13 <=> ! [X1,X0] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X1,sK0) | v4_pre_topc(sK4(X0,sK2),X1) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(sK2,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(sK4(X0,sK2),X1) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_13),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(sK4(X0,sK2),X1) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_13),
% 0.21/0.47    inference(resolution,[],[f114,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X2,sK2),X3) | v4_pre_topc(sK4(X2,sK2),X1) | ~m1_subset_1(sK4(X2,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v2_tops_2(sK2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_13),
% 0.21/0.47    inference(resolution,[],[f111,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X1,sK0) | v4_pre_topc(sK4(X0,sK2),X1) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_2(sK2,X0)) ) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~spl5_8 | spl5_13 | ~spl5_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f101,f110,f78])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl5_12 <=> ! [X0] : (~r2_hidden(X0,sK2) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | v4_pre_topc(sK4(X0,sK2),X1) | ~m1_pre_topc(X1,sK0) | ~l1_pre_topc(sK0)) ) | ~spl5_12),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X1))) | v4_pre_topc(sK4(X0,sK2),X1) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_12),
% 0.21/0.47    inference(resolution,[],[f104,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (v4_pre_topc(sK4(X0,sK2),sK0) | ~m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_2(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_12),
% 0.21/0.47    inference(resolution,[],[f102,f44])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_6 | spl5_12 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f97,f54,f101,f70,f78])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl5_2 <=> v2_tops_2(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl5_2),
% 0.21/0.47    inference(resolution,[],[f42,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    v2_tops_2(sK2,sK0) | ~spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~v2_tops_2(X1,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~spl5_7 | spl5_11 | ~spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f91,f62,f94,f74])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_4 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) ) | ~spl5_4),
% 0.21/0.47    inference(superposition,[],[f39,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl5_10 | ~spl5_3 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f66,f58,f88])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl5_3 <=> sK2 = sK3),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_3 | ~spl5_5)),
% 0.21/0.47    inference(superposition,[],[f67,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    sK2 = sK3 | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~spl5_9 | spl5_1 | ~spl5_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f81,f58,f50,f83])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl5_1 <=> v2_tops_2(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~v2_tops_2(sK2,sK1) | (spl5_1 | ~spl5_3)),
% 0.21/0.47    inference(forward_demodulation,[],[f51,f59])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~v2_tops_2(sK3,sK1) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f78])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    (((~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f23,f22,f21,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f74])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f70])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f66])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f62])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f58])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK2 = sK3),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f54])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v2_tops_2(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f50])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~v2_tops_2(sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18123)------------------------------
% 0.21/0.48  % (18123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18123)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18123)Memory used [KB]: 10746
% 0.21/0.48  % (18123)Time elapsed: 0.057 s
% 0.21/0.48  % (18123)------------------------------
% 0.21/0.48  % (18123)------------------------------
% 0.21/0.48  % (18116)Success in time 0.118 s
%------------------------------------------------------------------------------
