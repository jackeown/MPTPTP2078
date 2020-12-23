%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:29 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 192 expanded)
%              Number of leaves         :   23 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  413 ( 985 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f82,f105,f117,f133,f135,f147,f151,f208])).

fof(f208,plain,
    ( ~ spl5_6
    | ~ spl5_12
    | spl5_7
    | spl5_15
    | spl5_14 ),
    inference(avatar_split_clause,[],[f201,f145,f149,f80,f128,f70])).

fof(f70,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f128,plain,
    ( spl5_12
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f80,plain,
    ( spl5_7
  <=> v1_tops_2(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f149,plain,
    ( spl5_15
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f145,plain,
    ( spl5_14
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f201,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl5_14 ),
    inference(resolution,[],[f153,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
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
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(X0,sK2))
        | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X0) )
    | spl5_14 ),
    inference(resolution,[],[f146,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f146,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f151,plain,
    ( ~ spl5_5
    | ~ spl5_15
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f141,f131,f58,f149,f66])).

fof(f66,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f58,plain,
    ( spl5_3
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f131,plain,
    ( spl5_13
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1)
        | ~ v1_tops_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f141,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f132,plain,
    ( ! [X1] :
        ( ~ v1_tops_2(X1,sK0)
        | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f147,plain,
    ( ~ spl5_4
    | ~ spl5_14
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f140,f131,f54,f145,f62])).

fof(f62,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f54,plain,
    ( spl5_2
  <=> v1_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f140,plain,
    ( ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(resolution,[],[f132,f55])).

fof(f55,plain,
    ( v1_tops_2(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f135,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | spl5_12 ),
    inference(avatar_split_clause,[],[f134,f128,f62,f66])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_12 ),
    inference(resolution,[],[f129,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f129,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f133,plain,
    ( ~ spl5_12
    | spl5_13
    | spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f119,f115,f80,f131,f128])).

fof(f115,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f119,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1)
        | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f116,f81])).

fof(f81,plain,
    ( ~ v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( ~ spl5_6
    | spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f113,f103,f115,f70])).

fof(f103,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( ~ spl5_6
    | spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f100,f70,f103,f70])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f99,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f34,f71])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | ~ spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f74,f50,f80,f62,f66])).

fof(f50,plain,
    ( spl5_1
  <=> v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,
    ( ~ v1_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_1 ),
    inference(superposition,[],[f51,f39])).

fof(f51,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK2,sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X2,X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X2,sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v1_tops_2(X2,sK0)
            & v1_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v1_tops_2(X2,sK0)
          & v1_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v1_tops_2(X2,sK0)
        & v1_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v1_tops_2(sK2,sK0)
      & v1_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X2,X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & v1_tops_2(X1,X0) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tops_2)).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_vampire %s %d
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % WCLimit    : 600
% 0.15/0.37  % DateTime   : Tue Dec  1 11:54:59 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.24/0.49  % (2450)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.24/0.50  % (2450)Refutation found. Thanks to Tanya!
% 0.24/0.50  % SZS status Theorem for theBenchmark
% 0.24/0.50  % (2459)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.24/0.50  % (2457)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.24/0.50  % SZS output start Proof for theBenchmark
% 0.24/0.50  fof(f209,plain,(
% 0.24/0.50    $false),
% 0.24/0.50    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f82,f105,f117,f133,f135,f147,f151,f208])).
% 0.24/0.50  fof(f208,plain,(
% 0.24/0.50    ~spl5_6 | ~spl5_12 | spl5_7 | spl5_15 | spl5_14),
% 0.24/0.50    inference(avatar_split_clause,[],[f201,f145,f149,f80,f128,f70])).
% 0.24/0.50  fof(f70,plain,(
% 0.24/0.50    spl5_6 <=> l1_pre_topc(sK0)),
% 0.24/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.24/0.50  fof(f128,plain,(
% 0.24/0.50    spl5_12 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.24/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.24/0.50  fof(f80,plain,(
% 0.24/0.50    spl5_7 <=> v1_tops_2(k2_xboole_0(sK1,sK2),sK0)),
% 0.24/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.24/0.50  fof(f149,plain,(
% 0.24/0.50    spl5_15 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 0.24/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.24/0.50  fof(f145,plain,(
% 0.24/0.50    spl5_14 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 0.24/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.24/0.50  fof(f201,plain,(
% 0.24/0.50    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | spl5_14),
% 0.24/0.50    inference(resolution,[],[f153,f36])).
% 0.24/0.50  fof(f36,plain,(
% 0.24/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.24/0.50    inference(cnf_transformation,[],[f22])).
% 0.24/0.50  fof(f22,plain,(
% 0.24/0.50    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.24/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.24/0.50  fof(f21,plain,(
% 0.24/0.50    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.24/0.50    introduced(choice_axiom,[])).
% 0.24/0.50  fof(f20,plain,(
% 0.24/0.50    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.24/0.50    inference(rectify,[],[f19])).
% 0.24/0.50  fof(f19,plain,(
% 0.24/0.50    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.24/0.50    inference(nnf_transformation,[],[f10])).
% 0.24/0.50  fof(f10,plain,(
% 0.24/0.50    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.24/0.50    inference(flattening,[],[f9])).
% 0.24/0.50  fof(f9,plain,(
% 0.24/0.50    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.24/0.50    inference(ennf_transformation,[],[f4])).
% 0.24/0.50  fof(f4,axiom,(
% 0.24/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.24/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.24/0.50  fof(f153,plain,(
% 0.24/0.50    ( ! [X0] : (~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(X0,sK2)) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X0)) ) | spl5_14),
% 0.24/0.50    inference(resolution,[],[f146,f48])).
% 0.24/0.50  fof(f48,plain,(
% 0.24/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.24/0.50    inference(equality_resolution,[],[f40])).
% 0.24/0.50  fof(f40,plain,(
% 0.24/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.24/0.50    inference(cnf_transformation,[],[f27])).
% 0.24/0.50  fof(f27,plain,(
% 0.24/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.24/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.24/0.50  fof(f26,plain,(
% 0.24/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.24/0.50    introduced(choice_axiom,[])).
% 0.24/0.50  fof(f25,plain,(
% 0.24/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.24/0.50    inference(rectify,[],[f24])).
% 0.24/0.50  fof(f24,plain,(
% 0.24/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.24/0.50    inference(flattening,[],[f23])).
% 0.24/0.50  fof(f23,plain,(
% 0.24/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.24/0.50    inference(nnf_transformation,[],[f1])).
% 0.24/0.50  fof(f1,axiom,(
% 0.24/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.24/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.24/0.51  fof(f146,plain,(
% 0.24/0.51    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | spl5_14),
% 0.24/0.51    inference(avatar_component_clause,[],[f145])).
% 0.24/0.51  fof(f151,plain,(
% 0.24/0.51    ~spl5_5 | ~spl5_15 | ~spl5_3 | ~spl5_13),
% 0.24/0.51    inference(avatar_split_clause,[],[f141,f131,f58,f149,f66])).
% 0.24/0.51  fof(f66,plain,(
% 0.24/0.51    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.24/0.51  fof(f58,plain,(
% 0.24/0.51    spl5_3 <=> v1_tops_2(sK1,sK0)),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.24/0.51  fof(f131,plain,(
% 0.24/0.51    spl5_13 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1) | ~v1_tops_2(X1,sK0))),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.24/0.51  fof(f141,plain,(
% 0.24/0.51    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_3 | ~spl5_13)),
% 0.24/0.51    inference(resolution,[],[f132,f59])).
% 0.24/0.51  fof(f59,plain,(
% 0.24/0.51    v1_tops_2(sK1,sK0) | ~spl5_3),
% 0.24/0.51    inference(avatar_component_clause,[],[f58])).
% 0.24/0.51  fof(f132,plain,(
% 0.24/0.51    ( ! [X1] : (~v1_tops_2(X1,sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_13),
% 0.24/0.51    inference(avatar_component_clause,[],[f131])).
% 0.24/0.51  fof(f147,plain,(
% 0.24/0.51    ~spl5_4 | ~spl5_14 | ~spl5_2 | ~spl5_13),
% 0.24/0.51    inference(avatar_split_clause,[],[f140,f131,f54,f145,f62])).
% 0.24/0.51  fof(f62,plain,(
% 0.24/0.51    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.24/0.51  fof(f54,plain,(
% 0.24/0.51    spl5_2 <=> v1_tops_2(sK2,sK0)),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.24/0.51  fof(f140,plain,(
% 0.24/0.51    ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_2 | ~spl5_13)),
% 0.24/0.51    inference(resolution,[],[f132,f55])).
% 0.24/0.51  fof(f55,plain,(
% 0.24/0.51    v1_tops_2(sK2,sK0) | ~spl5_2),
% 0.24/0.51    inference(avatar_component_clause,[],[f54])).
% 0.24/0.51  fof(f135,plain,(
% 0.24/0.51    ~spl5_5 | ~spl5_4 | spl5_12),
% 0.24/0.51    inference(avatar_split_clause,[],[f134,f128,f62,f66])).
% 0.24/0.51  fof(f134,plain,(
% 0.24/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_12),
% 0.24/0.51    inference(resolution,[],[f129,f76])).
% 0.24/0.51  fof(f76,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f75])).
% 0.24/0.51  fof(f75,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.51    inference(superposition,[],[f38,f39])).
% 0.24/0.51  fof(f39,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.51    inference(cnf_transformation,[],[f14])).
% 0.24/0.51  fof(f14,plain,(
% 0.24/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.51    inference(flattening,[],[f13])).
% 0.24/0.51  fof(f13,plain,(
% 0.24/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.24/0.51    inference(ennf_transformation,[],[f3])).
% 0.24/0.51  fof(f3,axiom,(
% 0.24/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.24/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.24/0.51  fof(f38,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.24/0.51    inference(cnf_transformation,[],[f12])).
% 0.24/0.51  fof(f12,plain,(
% 0.24/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.24/0.51    inference(flattening,[],[f11])).
% 0.24/0.51  fof(f11,plain,(
% 0.24/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.24/0.51    inference(ennf_transformation,[],[f2])).
% 0.24/0.51  fof(f2,axiom,(
% 0.24/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.24/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.24/0.51  fof(f129,plain,(
% 0.24/0.51    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_12),
% 0.24/0.51    inference(avatar_component_clause,[],[f128])).
% 0.24/0.51  fof(f133,plain,(
% 0.24/0.51    ~spl5_12 | spl5_13 | spl5_7 | ~spl5_9),
% 0.24/0.51    inference(avatar_split_clause,[],[f119,f115,f80,f131,f128])).
% 0.24/0.51  fof(f115,plain,(
% 0.24/0.51    spl5_9 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | v1_tops_2(X0,sK0))),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.24/0.51  fof(f119,plain,(
% 0.24/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),X1) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (spl5_7 | ~spl5_9)),
% 0.24/0.51    inference(resolution,[],[f116,f81])).
% 0.24/0.51  fof(f81,plain,(
% 0.24/0.51    ~v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | spl5_7),
% 0.24/0.51    inference(avatar_component_clause,[],[f80])).
% 0.24/0.51  fof(f116,plain,(
% 0.24/0.51    ( ! [X0,X1] : (v1_tops_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X1,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_9),
% 0.24/0.51    inference(avatar_component_clause,[],[f115])).
% 0.24/0.51  fof(f117,plain,(
% 0.24/0.51    ~spl5_6 | spl5_9 | ~spl5_8),
% 0.24/0.51    inference(avatar_split_clause,[],[f113,f103,f115,f70])).
% 0.24/0.51  fof(f103,plain,(
% 0.24/0.51    spl5_8 <=> ! [X1,X0] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.24/0.51  fof(f113,plain,(
% 0.24/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl5_8),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.24/0.51  fof(f112,plain,(
% 0.24/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl5_8),
% 0.24/0.51    inference(resolution,[],[f104,f35])).
% 0.24/0.51  fof(f35,plain,(
% 0.24/0.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f104,plain,(
% 0.24/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl5_8),
% 0.24/0.51    inference(avatar_component_clause,[],[f103])).
% 0.24/0.51  fof(f105,plain,(
% 0.24/0.51    ~spl5_6 | spl5_8 | ~spl5_6),
% 0.24/0.51    inference(avatar_split_clause,[],[f100,f70,f103,f70])).
% 0.24/0.51  fof(f100,plain,(
% 0.24/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | v1_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl5_6),
% 0.24/0.51    inference(resolution,[],[f99,f37])).
% 0.24/0.51  fof(f37,plain,(
% 0.24/0.51    ( ! [X0,X1] : (~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f99,plain,(
% 0.24/0.51    ( ! [X0,X1] : (v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X1)) ) | ~spl5_6),
% 0.24/0.51    inference(resolution,[],[f34,f71])).
% 0.24/0.51  fof(f71,plain,(
% 0.24/0.51    l1_pre_topc(sK0) | ~spl5_6),
% 0.24/0.51    inference(avatar_component_clause,[],[f70])).
% 0.24/0.51  fof(f34,plain,(
% 0.24/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v3_pre_topc(X3,X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f82,plain,(
% 0.24/0.51    ~spl5_5 | ~spl5_4 | ~spl5_7 | spl5_1),
% 0.24/0.51    inference(avatar_split_clause,[],[f74,f50,f80,f62,f66])).
% 0.24/0.51  fof(f50,plain,(
% 0.24/0.51    spl5_1 <=> v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.24/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.24/0.51  fof(f74,plain,(
% 0.24/0.51    ~v1_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_1),
% 0.24/0.51    inference(superposition,[],[f51,f39])).
% 0.24/0.51  fof(f51,plain,(
% 0.24/0.51    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl5_1),
% 0.24/0.51    inference(avatar_component_clause,[],[f50])).
% 0.24/0.51  fof(f72,plain,(
% 0.24/0.51    spl5_6),
% 0.24/0.51    inference(avatar_split_clause,[],[f28,f70])).
% 0.24/0.51  fof(f28,plain,(
% 0.24/0.51    l1_pre_topc(sK0)),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  fof(f18,plain,(
% 0.24/0.51    ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK2,sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.24/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.24/0.51  fof(f15,plain,(
% 0.24/0.51    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X2,sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.24/0.51    introduced(choice_axiom,[])).
% 0.24/0.51  fof(f16,plain,(
% 0.24/0.51    ? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X2,sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(X2,sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.24/0.51    introduced(choice_axiom,[])).
% 0.24/0.51  fof(f17,plain,(
% 0.24/0.51    ? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v1_tops_2(X2,sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK2,sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.24/0.51    introduced(choice_axiom,[])).
% 0.24/0.51  fof(f8,plain,(
% 0.24/0.51    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X2,X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.24/0.51    inference(flattening,[],[f7])).
% 0.24/0.51  fof(f7,plain,(
% 0.24/0.51    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v1_tops_2(X2,X0) & v1_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.24/0.51    inference(ennf_transformation,[],[f6])).
% 0.24/0.51  fof(f6,negated_conjecture,(
% 0.24/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.24/0.51    inference(negated_conjecture,[],[f5])).
% 0.24/0.51  fof(f5,conjecture,(
% 0.24/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.24/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tops_2)).
% 0.24/0.51  fof(f68,plain,(
% 0.24/0.51    spl5_5),
% 0.24/0.51    inference(avatar_split_clause,[],[f29,f66])).
% 0.24/0.51  fof(f29,plain,(
% 0.24/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  fof(f64,plain,(
% 0.24/0.51    spl5_4),
% 0.24/0.51    inference(avatar_split_clause,[],[f30,f62])).
% 0.24/0.51  fof(f30,plain,(
% 0.24/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  fof(f60,plain,(
% 0.24/0.51    spl5_3),
% 0.24/0.51    inference(avatar_split_clause,[],[f31,f58])).
% 0.24/0.51  fof(f31,plain,(
% 0.24/0.51    v1_tops_2(sK1,sK0)),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  fof(f56,plain,(
% 0.24/0.51    spl5_2),
% 0.24/0.51    inference(avatar_split_clause,[],[f32,f54])).
% 0.24/0.51  fof(f32,plain,(
% 0.24/0.51    v1_tops_2(sK2,sK0)),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  fof(f52,plain,(
% 0.24/0.51    ~spl5_1),
% 0.24/0.51    inference(avatar_split_clause,[],[f33,f50])).
% 0.24/0.51  fof(f33,plain,(
% 0.24/0.51    ~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.24/0.51    inference(cnf_transformation,[],[f18])).
% 0.24/0.51  % SZS output end Proof for theBenchmark
% 0.24/0.51  % (2450)------------------------------
% 0.24/0.51  % (2450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.51  % (2450)Termination reason: Refutation
% 0.24/0.51  
% 0.24/0.51  % (2450)Memory used [KB]: 10746
% 0.24/0.51  % (2450)Time elapsed: 0.058 s
% 0.24/0.51  % (2450)------------------------------
% 0.24/0.51  % (2450)------------------------------
% 0.24/0.51  % (2451)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.24/0.51  % (2443)Success in time 0.126 s
%------------------------------------------------------------------------------
