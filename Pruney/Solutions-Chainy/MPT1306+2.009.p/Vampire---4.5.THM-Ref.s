%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:37 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 208 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  433 ( 979 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f88,f97,f103,f111,f129,f135,f141,f372,f397,f399])).

fof(f399,plain,
    ( ~ spl6_5
    | ~ spl6_13
    | spl6_6
    | spl6_12 ),
    inference(avatar_split_clause,[],[f152,f124,f86,f127,f80])).

fof(f80,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f127,plain,
    ( spl6_13
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f86,plain,
    ( spl6_6
  <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f124,plain,
    ( spl6_12
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f152,plain,
    ( v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl6_12 ),
    inference(resolution,[],[f150,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f150,plain,
    ( ! [X2] : ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,X2))
    | spl6_12 ),
    inference(resolution,[],[f125,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f125,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f397,plain,
    ( spl6_14
    | spl6_16 ),
    inference(avatar_split_clause,[],[f390,f370,f133])).

fof(f133,plain,
    ( spl6_14
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f370,plain,
    ( spl6_16
  <=> r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f390,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(resolution,[],[f380,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f380,plain,
    ( ! [X3] : ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k3_xboole_0(X3,sK2))
    | spl6_16 ),
    inference(resolution,[],[f371,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f371,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f370])).

fof(f372,plain,
    ( ~ spl6_16
    | ~ spl6_3
    | spl6_15 ),
    inference(avatar_split_clause,[],[f365,f139,f72,f370])).

fof(f72,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f139,plain,
    ( spl6_15
  <=> r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f365,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2)
    | ~ spl6_3
    | spl6_15 ),
    inference(resolution,[],[f182,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),X0) )
    | spl6_15 ),
    inference(resolution,[],[f140,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f140,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,
    ( ~ spl6_15
    | spl6_14 ),
    inference(avatar_split_clause,[],[f136,f133,f139])).

fof(f136,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_14 ),
    inference(resolution,[],[f134,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( ~ spl6_14
    | spl6_13 ),
    inference(avatar_split_clause,[],[f130,f127,f133])).

fof(f130,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13 ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f128,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f113,f109,f86,f127,f124])).

fof(f109,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f113,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | spl6_6
    | ~ spl6_9 ),
    inference(resolution,[],[f110,f87])).

fof(f87,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f110,plain,
    ( ! [X0] :
        ( v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),sK1) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f111,plain,
    ( ~ spl6_5
    | spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f107,f101,f109,f80])).

fof(f101,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | v2_tops_2(X0,sK0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( ~ spl6_4
    | spl6_8
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f98,f95,f68,f101,f76])).

fof(f76,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f68,plain,
    ( spl6_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f95,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),sK1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f96,f69])).

fof(f69,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0)
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( ~ spl6_5
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f92,f80,f95,f80])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK3(sK0,X0),X1)
        | v2_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f42,f81])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f83,f64,f86,f72])).

fof(f64,plain,
    ( spl6_1
  <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f83,plain,
    ( ~ v2_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_1 ),
    inference(superposition,[],[f65,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f65,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

fof(f78,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f41,f64])).

fof(f41,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31411)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (31417)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (31396)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (31412)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (31390)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (31389)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (31391)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (31395)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (31392)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (31409)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (31394)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (31415)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (31418)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (31404)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (31407)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (31401)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (31408)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (31406)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (31405)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (31398)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (31399)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (31397)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (31393)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (31403)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.54  % (31416)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (31413)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (31414)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (31410)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (31415)Refutation not found, incomplete strategy% (31415)------------------------------
% 1.36/0.55  % (31415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (31415)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (31415)Memory used [KB]: 10746
% 1.36/0.55  % (31415)Time elapsed: 0.134 s
% 1.36/0.55  % (31415)------------------------------
% 1.36/0.55  % (31415)------------------------------
% 1.36/0.55  % (31402)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (31406)Refutation not found, incomplete strategy% (31406)------------------------------
% 1.36/0.55  % (31406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (31406)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (31406)Memory used [KB]: 10618
% 1.36/0.55  % (31406)Time elapsed: 0.143 s
% 1.36/0.55  % (31406)------------------------------
% 1.36/0.55  % (31406)------------------------------
% 1.36/0.56  % (31399)Refutation not found, incomplete strategy% (31399)------------------------------
% 1.36/0.56  % (31399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (31399)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (31399)Memory used [KB]: 10618
% 1.36/0.56  % (31399)Time elapsed: 0.126 s
% 1.36/0.56  % (31399)------------------------------
% 1.36/0.56  % (31399)------------------------------
% 1.36/0.56  % (31400)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.56  % (31400)Refutation not found, incomplete strategy% (31400)------------------------------
% 1.36/0.56  % (31400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (31400)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (31400)Memory used [KB]: 10618
% 1.36/0.56  % (31400)Time elapsed: 0.153 s
% 1.36/0.56  % (31400)------------------------------
% 1.36/0.56  % (31400)------------------------------
% 1.55/0.57  % (31408)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f400,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f88,f97,f103,f111,f129,f135,f141,f372,f397,f399])).
% 1.55/0.57  fof(f399,plain,(
% 1.55/0.57    ~spl6_5 | ~spl6_13 | spl6_6 | spl6_12),
% 1.55/0.57    inference(avatar_split_clause,[],[f152,f124,f86,f127,f80])).
% 1.55/0.57  fof(f80,plain,(
% 1.55/0.57    spl6_5 <=> l1_pre_topc(sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.55/0.57  fof(f127,plain,(
% 1.55/0.57    spl6_13 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.55/0.57  fof(f86,plain,(
% 1.55/0.57    spl6_6 <=> v2_tops_2(k3_xboole_0(sK1,sK2),sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.55/0.57  fof(f124,plain,(
% 1.55/0.57    spl6_12 <=> r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.55/0.57  fof(f152,plain,(
% 1.55/0.57    v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | spl6_12),
% 1.55/0.57    inference(resolution,[],[f150,f44])).
% 1.55/0.57  fof(f44,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f26])).
% 1.55/0.57  fof(f26,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f24,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(rectify,[],[f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(nnf_transformation,[],[f13])).
% 1.55/0.57  fof(f13,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(flattening,[],[f12])).
% 1.55/0.57  fof(f12,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.55/0.57    inference(ennf_transformation,[],[f7])).
% 1.55/0.57  fof(f7,axiom,(
% 1.55/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 1.55/0.57  fof(f150,plain,(
% 1.55/0.57    ( ! [X2] : (~r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,X2))) ) | spl6_12),
% 1.55/0.57    inference(resolution,[],[f125,f62])).
% 1.55/0.57  fof(f62,plain,(
% 1.55/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(equality_resolution,[],[f54])).
% 1.55/0.57  fof(f54,plain,(
% 1.55/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.55/0.57    inference(cnf_transformation,[],[f36])).
% 1.55/0.57  fof(f36,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 1.55/0.57  fof(f35,plain,(
% 1.55/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f34,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(rectify,[],[f33])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(flattening,[],[f32])).
% 1.55/0.57  fof(f32,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.55/0.57    inference(nnf_transformation,[],[f2])).
% 1.55/0.57  fof(f2,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.55/0.57  fof(f125,plain,(
% 1.55/0.57    ~r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1) | spl6_12),
% 1.55/0.57    inference(avatar_component_clause,[],[f124])).
% 1.55/0.57  fof(f397,plain,(
% 1.55/0.57    spl6_14 | spl6_16),
% 1.55/0.57    inference(avatar_split_clause,[],[f390,f370,f133])).
% 1.55/0.57  fof(f133,plain,(
% 1.55/0.57    spl6_14 <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.55/0.57  fof(f370,plain,(
% 1.55/0.57    spl6_16 <=> r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.55/0.57  fof(f390,plain,(
% 1.55/0.57    r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 1.55/0.57    inference(resolution,[],[f380,f48])).
% 1.55/0.57  fof(f48,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.55/0.57  fof(f29,plain,(
% 1.55/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.55/0.57    introduced(choice_axiom,[])).
% 1.55/0.57  fof(f28,plain,(
% 1.55/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.57    inference(rectify,[],[f27])).
% 1.55/0.57  fof(f27,plain,(
% 1.55/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.57    inference(nnf_transformation,[],[f15])).
% 1.55/0.57  fof(f15,plain,(
% 1.55/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.57  fof(f380,plain,(
% 1.55/0.57    ( ! [X3] : (~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k3_xboole_0(X3,sK2))) ) | spl6_16),
% 1.55/0.57    inference(resolution,[],[f371,f61])).
% 1.55/0.57  fof(f61,plain,(
% 1.55/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(equality_resolution,[],[f55])).
% 1.55/0.58  fof(f55,plain,(
% 1.55/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f36])).
% 1.55/0.58  fof(f371,plain,(
% 1.55/0.58    ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2) | spl6_16),
% 1.55/0.58    inference(avatar_component_clause,[],[f370])).
% 1.55/0.58  fof(f372,plain,(
% 1.55/0.58    ~spl6_16 | ~spl6_3 | spl6_15),
% 1.55/0.58    inference(avatar_split_clause,[],[f365,f139,f72,f370])).
% 1.55/0.58  fof(f72,plain,(
% 1.55/0.58    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.55/0.58  fof(f139,plain,(
% 1.55/0.58    spl6_15 <=> r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.55/0.58  fof(f365,plain,(
% 1.55/0.58    ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),sK2) | (~spl6_3 | spl6_15)),
% 1.55/0.58    inference(resolution,[],[f182,f73])).
% 1.55/0.58  fof(f73,plain,(
% 1.55/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_3),
% 1.55/0.58    inference(avatar_component_clause,[],[f72])).
% 1.55/0.58  fof(f182,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),X0)) ) | spl6_15),
% 1.55/0.58    inference(resolution,[],[f140,f46])).
% 1.55/0.58  fof(f46,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f14])).
% 1.55/0.58  fof(f14,plain,(
% 1.55/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.55/0.58  fof(f140,plain,(
% 1.55/0.58    ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_15),
% 1.55/0.58    inference(avatar_component_clause,[],[f139])).
% 1.55/0.58  fof(f141,plain,(
% 1.55/0.58    ~spl6_15 | spl6_14),
% 1.55/0.58    inference(avatar_split_clause,[],[f136,f133,f139])).
% 1.55/0.58  fof(f136,plain,(
% 1.55/0.58    ~r2_hidden(sK4(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_14),
% 1.55/0.58    inference(resolution,[],[f134,f49])).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f30])).
% 1.55/0.58  fof(f134,plain,(
% 1.55/0.58    ~r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_14),
% 1.55/0.58    inference(avatar_component_clause,[],[f133])).
% 1.55/0.58  fof(f135,plain,(
% 1.55/0.58    ~spl6_14 | spl6_13),
% 1.55/0.58    inference(avatar_split_clause,[],[f130,f127,f133])).
% 1.55/0.58  fof(f130,plain,(
% 1.55/0.58    ~r1_tarski(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_13),
% 1.55/0.58    inference(resolution,[],[f128,f51])).
% 1.55/0.58  fof(f51,plain,(
% 1.55/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f31])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.55/0.58    inference(nnf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.58  fof(f128,plain,(
% 1.55/0.58    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_13),
% 1.55/0.58    inference(avatar_component_clause,[],[f127])).
% 1.55/0.58  fof(f129,plain,(
% 1.55/0.58    ~spl6_12 | ~spl6_13 | spl6_6 | ~spl6_9),
% 1.55/0.58    inference(avatar_split_clause,[],[f113,f109,f86,f127,f124])).
% 1.55/0.58  fof(f109,plain,(
% 1.55/0.58    spl6_9 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.55/0.58  fof(f113,plain,(
% 1.55/0.58    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK1,sK2)),sK1) | (spl6_6 | ~spl6_9)),
% 1.55/0.58    inference(resolution,[],[f110,f87])).
% 1.55/0.58  fof(f87,plain,(
% 1.55/0.58    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | spl6_6),
% 1.55/0.58    inference(avatar_component_clause,[],[f86])).
% 1.55/0.58  fof(f110,plain,(
% 1.55/0.58    ( ! [X0] : (v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1)) ) | ~spl6_9),
% 1.55/0.58    inference(avatar_component_clause,[],[f109])).
% 1.55/0.58  fof(f111,plain,(
% 1.55/0.58    ~spl6_5 | spl6_9 | ~spl6_8),
% 1.55/0.58    inference(avatar_split_clause,[],[f107,f101,f109,f80])).
% 1.55/0.58  fof(f101,plain,(
% 1.55/0.58    spl6_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.55/0.58  fof(f107,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl6_8),
% 1.55/0.58    inference(duplicate_literal_removal,[],[f104])).
% 1.55/0.58  fof(f104,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl6_8),
% 1.55/0.58    inference(resolution,[],[f102,f43])).
% 1.55/0.58  fof(f43,plain,(
% 1.55/0.58    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f26])).
% 1.55/0.58  fof(f102,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),sK1) | v2_tops_2(X0,sK0)) ) | ~spl6_8),
% 1.55/0.58    inference(avatar_component_clause,[],[f101])).
% 1.55/0.58  fof(f103,plain,(
% 1.55/0.58    ~spl6_4 | spl6_8 | ~spl6_2 | ~spl6_7),
% 1.55/0.58    inference(avatar_split_clause,[],[f98,f95,f68,f101,f76])).
% 1.55/0.58  fof(f76,plain,(
% 1.55/0.58    spl6_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.55/0.58  fof(f68,plain,(
% 1.55/0.58    spl6_2 <=> v2_tops_2(sK1,sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.55/0.58  fof(f95,plain,(
% 1.55/0.58    spl6_7 <=> ! [X1,X0] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.55/0.58  fof(f98,plain,(
% 1.55/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),sK1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (~spl6_2 | ~spl6_7)),
% 1.55/0.58    inference(resolution,[],[f96,f69])).
% 1.55/0.58  fof(f69,plain,(
% 1.55/0.58    v2_tops_2(sK1,sK0) | ~spl6_2),
% 1.55/0.58    inference(avatar_component_clause,[],[f68])).
% 1.55/0.58  fof(f96,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~v2_tops_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X0,sK0) | ~r2_hidden(sK3(sK0,X0),X1) | ~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl6_7),
% 1.55/0.58    inference(avatar_component_clause,[],[f95])).
% 1.55/0.58  fof(f97,plain,(
% 1.55/0.58    ~spl6_5 | spl6_7 | ~spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f92,f80,f95,f80])).
% 1.55/0.58  fof(f92,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK3(sK0,X0),X1) | v2_tops_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f91,f45])).
% 1.55/0.58  fof(f45,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f26])).
% 1.55/0.58  fof(f91,plain,(
% 1.55/0.58    ( ! [X0,X1] : (v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X0,X1)) ) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f42,f81])).
% 1.55/0.58  fof(f81,plain,(
% 1.55/0.58    l1_pre_topc(sK0) | ~spl6_5),
% 1.55/0.58    inference(avatar_component_clause,[],[f80])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v4_pre_topc(X3,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f26])).
% 1.55/0.58  fof(f88,plain,(
% 1.55/0.58    ~spl6_3 | ~spl6_6 | spl6_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f83,f64,f86,f72])).
% 1.55/0.58  fof(f64,plain,(
% 1.55/0.58    spl6_1 <=> v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.55/0.58  fof(f83,plain,(
% 1.55/0.58    ~v2_tops_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_1),
% 1.55/0.58    inference(superposition,[],[f65,f52])).
% 1.55/0.58  fof(f52,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f16])).
% 1.55/0.58  fof(f16,plain,(
% 1.55/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f4])).
% 1.55/0.58  fof(f4,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl6_1),
% 1.55/0.58    inference(avatar_component_clause,[],[f64])).
% 1.55/0.58  fof(f82,plain,(
% 1.55/0.58    spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f37,f80])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    l1_pre_topc(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f22])).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f21,plain,(
% 1.55/0.58    ? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f11,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.55/0.58    inference(flattening,[],[f10])).
% 1.55/0.58  fof(f10,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f9])).
% 1.55/0.58  fof(f9,negated_conjecture,(
% 1.55/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.55/0.58    inference(negated_conjecture,[],[f8])).
% 1.55/0.58  fof(f8,conjecture,(
% 1.55/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).
% 1.55/0.58  fof(f78,plain,(
% 1.55/0.58    spl6_4),
% 1.55/0.58    inference(avatar_split_clause,[],[f38,f76])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.58    inference(cnf_transformation,[],[f22])).
% 1.55/0.58  fof(f74,plain,(
% 1.55/0.58    spl6_3),
% 1.55/0.58    inference(avatar_split_clause,[],[f39,f72])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.55/0.58    inference(cnf_transformation,[],[f22])).
% 1.55/0.58  fof(f70,plain,(
% 1.55/0.58    spl6_2),
% 1.55/0.58    inference(avatar_split_clause,[],[f40,f68])).
% 1.55/0.58  fof(f40,plain,(
% 1.55/0.58    v2_tops_2(sK1,sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f22])).
% 1.55/0.58  fof(f66,plain,(
% 1.55/0.58    ~spl6_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f41,f64])).
% 1.55/0.58  fof(f41,plain,(
% 1.55/0.58    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f22])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (31408)------------------------------
% 1.55/0.58  % (31408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (31408)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (31408)Memory used [KB]: 11001
% 1.55/0.58  % (31408)Time elapsed: 0.152 s
% 1.55/0.58  % (31408)------------------------------
% 1.55/0.58  % (31408)------------------------------
% 1.55/0.58  % (31384)Success in time 0.209 s
%------------------------------------------------------------------------------
