%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:56 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 285 expanded)
%              Number of leaves         :   33 ( 130 expanded)
%              Depth                    :    9
%              Number of atoms          :  549 (1485 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f76,f80,f84,f88,f92,f96,f100,f111,f128,f198,f216,f248,f251,f413,f438,f463,f479,f490,f625])).

fof(f625,plain,
    ( ~ spl6_44
    | spl6_17
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f619,f488,f214,f408])).

fof(f408,plain,
    ( spl6_44
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f214,plain,
    ( spl6_17
  <=> r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f488,plain,
    ( spl6_57
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f619,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_17
    | ~ spl6_57 ),
    inference(resolution,[],[f489,f220])).

fof(f220,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
        | ~ r2_hidden(sK1,X1) )
    | spl6_17 ),
    inference(resolution,[],[f215,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f215,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f214])).

fof(f489,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f488])).

fof(f490,plain,
    ( spl6_57
    | ~ spl6_5
    | ~ spl6_16
    | ~ spl6_7
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f484,f477,f90,f211,f82,f488])).

fof(f82,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f211,plain,
    ( spl6_16
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f90,plain,
    ( spl6_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f477,plain,
    ( spl6_55
  <=> r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f484,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl6_7
    | ~ spl6_55 ),
    inference(resolution,[],[f478,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f47,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f478,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f477])).

fof(f479,plain,
    ( spl6_55
    | spl6_52 ),
    inference(avatar_split_clause,[],[f472,f461,f477])).

fof(f461,plain,
    ( spl6_52
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f472,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | spl6_52 ),
    inference(resolution,[],[f462,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f462,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f461])).

fof(f463,plain,
    ( ~ spl6_52
    | spl6_45 ),
    inference(avatar_split_clause,[],[f455,f411,f461])).

fof(f411,plain,
    ( spl6_45
  <=> r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f455,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2)
    | spl6_45 ),
    inference(resolution,[],[f412,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f412,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))
    | spl6_45 ),
    inference(avatar_component_clause,[],[f411])).

fof(f438,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | ~ spl6_11
    | spl6_44 ),
    inference(avatar_split_clause,[],[f430,f408,f126,f86,f74])).

fof(f74,plain,
    ( spl6_3
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f86,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f126,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f430,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_6
    | ~ spl6_11
    | spl6_44 ),
    inference(resolution,[],[f409,f129])).

fof(f129,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1) )
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f127,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,X1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f409,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f408])).

fof(f413,plain,
    ( ~ spl6_44
    | ~ spl6_45
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f401,f246,f82,f411,f408])).

fof(f246,plain,
    ( spl6_21
  <=> ! [X1] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X1))
        | ~ r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f401,plain,
    ( ~ r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(resolution,[],[f247,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f247,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X1)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f251,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | spl6_16 ),
    inference(avatar_split_clause,[],[f249,f211,f78,f82])).

fof(f78,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f249,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(resolution,[],[f212,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f212,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f248,plain,
    ( ~ spl6_16
    | spl6_21
    | ~ spl6_7
    | spl6_17 ),
    inference(avatar_split_clause,[],[f244,f214,f90,f246,f211])).

fof(f244,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) )
    | ~ spl6_7
    | spl6_17 ),
    inference(resolution,[],[f220,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK4(X1,X0),X0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f142,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f216,plain,
    ( ~ spl6_16
    | ~ spl6_17
    | ~ spl6_6
    | spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f201,f196,f109,f86,f214,f211])).

fof(f109,plain,
    ( spl6_10
  <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f196,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f201,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6
    | spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f199,f110])).

fof(f110,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f199,plain,
    ( ! [X0] :
        ( m1_connsp_2(X0,sK0,sK1)
        | ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(resolution,[],[f197,f87])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f194,f94,f196,f90,f98])).

fof(f98,plain,
    ( spl6_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f94,plain,
    ( spl6_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | m1_connsp_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f49,f95])).

fof(f95,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f128,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f122,f94,f126,f90,f98])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f101,f95])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | ~ spl6_10
    | spl6_1 ),
    inference(avatar_split_clause,[],[f103,f66,f109,f78,f82])).

fof(f66,plain,
    ( spl6_1
  <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f103,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(superposition,[],[f67,f55])).

fof(f67,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f100,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f38,f98])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    & m1_connsp_2(sK3,sK0,sK1)
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  & m1_connsp_2(X3,sK0,X1)
                  & m1_connsp_2(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                & m1_connsp_2(X3,sK0,X1)
                & m1_connsp_2(X2,sK0,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              & m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(X2,sK0,sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
            & m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(X2,sK0,sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          & m1_connsp_2(X3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
        & m1_connsp_2(X3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      & m1_connsp_2(sK3,sK0,sK1)
      & m1_connsp_2(sK2,sK0,sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f96,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f39,f94])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f40,f90])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f46,f66])).

fof(f46,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24632)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (24650)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (24649)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (24648)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (24641)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (24640)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (24633)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (24636)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (24635)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (24628)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (24630)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (24629)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.58  % (24627)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.59  % (24644)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.59  % (24631)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.60  % (24653)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.60  % (24655)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.74/0.60  % (24652)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.74/0.60  % (24651)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.74/0.61  % (24654)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.74/0.61  % (24647)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.74/0.61  % (24637)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.74/0.61  % (24626)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.74/0.61  % (24638)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.61  % (24645)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.74/0.61  % (24646)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.74/0.61  % (24639)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.06/0.63  % (24642)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.06/0.64  % (24634)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.06/0.65  % (24643)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.06/0.65  % (24643)Refutation not found, incomplete strategy% (24643)------------------------------
% 2.06/0.65  % (24643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.65  % (24643)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.65  
% 2.06/0.65  % (24643)Memory used [KB]: 10618
% 2.06/0.65  % (24643)Time elapsed: 0.228 s
% 2.06/0.65  % (24643)------------------------------
% 2.06/0.65  % (24643)------------------------------
% 2.40/0.67  % (24645)Refutation found. Thanks to Tanya!
% 2.40/0.67  % SZS status Theorem for theBenchmark
% 2.40/0.67  % SZS output start Proof for theBenchmark
% 2.40/0.67  fof(f644,plain,(
% 2.40/0.67    $false),
% 2.40/0.67    inference(avatar_sat_refutation,[],[f68,f76,f80,f84,f88,f92,f96,f100,f111,f128,f198,f216,f248,f251,f413,f438,f463,f479,f490,f625])).
% 2.40/0.67  fof(f625,plain,(
% 2.40/0.67    ~spl6_44 | spl6_17 | ~spl6_57),
% 2.40/0.67    inference(avatar_split_clause,[],[f619,f488,f214,f408])).
% 2.40/0.67  fof(f408,plain,(
% 2.40/0.67    spl6_44 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 2.40/0.67  fof(f214,plain,(
% 2.40/0.67    spl6_17 <=> r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.40/0.67  fof(f488,plain,(
% 2.40/0.67    spl6_57 <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 2.40/0.67  fof(f619,plain,(
% 2.40/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl6_17 | ~spl6_57)),
% 2.40/0.67    inference(resolution,[],[f489,f220])).
% 2.40/0.67  fof(f220,plain,(
% 2.40/0.67    ( ! [X1] : (~r1_tarski(X1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~r2_hidden(sK1,X1)) ) | spl6_17),
% 2.40/0.67    inference(resolution,[],[f215,f51])).
% 2.40/0.67  fof(f51,plain,(
% 2.40/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f32])).
% 2.40/0.67  fof(f32,plain,(
% 2.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 2.40/0.67  fof(f31,plain,(
% 2.40/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f30,plain,(
% 2.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.67    inference(rectify,[],[f29])).
% 2.40/0.67  fof(f29,plain,(
% 2.40/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.67    inference(nnf_transformation,[],[f18])).
% 2.40/0.67  fof(f18,plain,(
% 2.40/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.67    inference(ennf_transformation,[],[f1])).
% 2.40/0.67  fof(f1,axiom,(
% 2.40/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.67  fof(f215,plain,(
% 2.40/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | spl6_17),
% 2.40/0.67    inference(avatar_component_clause,[],[f214])).
% 2.40/0.67  fof(f489,plain,(
% 2.40/0.67    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~spl6_57),
% 2.40/0.67    inference(avatar_component_clause,[],[f488])).
% 2.40/0.67  fof(f490,plain,(
% 2.40/0.67    spl6_57 | ~spl6_5 | ~spl6_16 | ~spl6_7 | ~spl6_55),
% 2.40/0.67    inference(avatar_split_clause,[],[f484,f477,f90,f211,f82,f488])).
% 2.40/0.67  fof(f82,plain,(
% 2.40/0.67    spl6_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.40/0.67  fof(f211,plain,(
% 2.40/0.67    spl6_16 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.40/0.67  fof(f90,plain,(
% 2.40/0.67    spl6_7 <=> l1_pre_topc(sK0)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.40/0.67  fof(f477,plain,(
% 2.40/0.67    spl6_55 <=> r1_tarski(sK2,k2_xboole_0(sK2,sK3))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 2.40/0.67  fof(f484,plain,(
% 2.40/0.67    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | (~spl6_7 | ~spl6_55)),
% 2.40/0.67    inference(resolution,[],[f478,f142])).
% 2.40/0.67  fof(f142,plain,(
% 2.40/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) ) | ~spl6_7),
% 2.40/0.67    inference(resolution,[],[f47,f91])).
% 2.40/0.67  fof(f91,plain,(
% 2.40/0.67    l1_pre_topc(sK0) | ~spl6_7),
% 2.40/0.67    inference(avatar_component_clause,[],[f90])).
% 2.40/0.67  fof(f47,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 2.40/0.67    inference(cnf_transformation,[],[f13])).
% 2.40/0.67  fof(f13,plain,(
% 2.40/0.67    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.67    inference(flattening,[],[f12])).
% 2.40/0.67  fof(f12,plain,(
% 2.40/0.67    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.67    inference(ennf_transformation,[],[f5])).
% 2.40/0.67  fof(f5,axiom,(
% 2.40/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.40/0.67  fof(f478,plain,(
% 2.40/0.67    r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | ~spl6_55),
% 2.40/0.67    inference(avatar_component_clause,[],[f477])).
% 2.40/0.67  fof(f479,plain,(
% 2.40/0.67    spl6_55 | spl6_52),
% 2.40/0.67    inference(avatar_split_clause,[],[f472,f461,f477])).
% 2.40/0.67  fof(f461,plain,(
% 2.40/0.67    spl6_52 <=> r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 2.40/0.67  fof(f472,plain,(
% 2.40/0.67    r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | spl6_52),
% 2.40/0.67    inference(resolution,[],[f462,f52])).
% 2.40/0.67  fof(f52,plain,(
% 2.40/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f32])).
% 2.40/0.67  fof(f462,plain,(
% 2.40/0.67    ~r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2) | spl6_52),
% 2.40/0.67    inference(avatar_component_clause,[],[f461])).
% 2.40/0.67  fof(f463,plain,(
% 2.40/0.67    ~spl6_52 | spl6_45),
% 2.40/0.67    inference(avatar_split_clause,[],[f455,f411,f461])).
% 2.40/0.67  fof(f411,plain,(
% 2.40/0.67    spl6_45 <=> r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.40/0.67  fof(f455,plain,(
% 2.40/0.67    ~r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),sK2) | spl6_45),
% 2.40/0.67    inference(resolution,[],[f412,f63])).
% 2.40/0.67  fof(f63,plain,(
% 2.40/0.67    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 2.40/0.67    inference(equality_resolution,[],[f57])).
% 2.40/0.67  fof(f57,plain,(
% 2.40/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.40/0.67    inference(cnf_transformation,[],[f37])).
% 2.40/0.67  fof(f37,plain,(
% 2.40/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 2.40/0.67  fof(f36,plain,(
% 2.40/0.67    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f35,plain,(
% 2.40/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.67    inference(rectify,[],[f34])).
% 2.40/0.67  fof(f34,plain,(
% 2.40/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.67    inference(flattening,[],[f33])).
% 2.40/0.67  fof(f33,plain,(
% 2.40/0.67    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.40/0.67    inference(nnf_transformation,[],[f2])).
% 2.40/0.67  fof(f2,axiom,(
% 2.40/0.67    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.40/0.67  fof(f412,plain,(
% 2.40/0.67    ~r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) | spl6_45),
% 2.40/0.67    inference(avatar_component_clause,[],[f411])).
% 2.40/0.67  fof(f438,plain,(
% 2.40/0.67    ~spl6_3 | ~spl6_6 | ~spl6_11 | spl6_44),
% 2.40/0.67    inference(avatar_split_clause,[],[f430,f408,f126,f86,f74])).
% 2.40/0.67  fof(f74,plain,(
% 2.40/0.67    spl6_3 <=> m1_connsp_2(sK2,sK0,sK1)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.40/0.67  fof(f86,plain,(
% 2.40/0.67    spl6_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.40/0.67  fof(f126,plain,(
% 2.40/0.67    spl6_11 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 2.40/0.67  fof(f430,plain,(
% 2.40/0.67    ~m1_connsp_2(sK2,sK0,sK1) | (~spl6_6 | ~spl6_11 | spl6_44)),
% 2.40/0.67    inference(resolution,[],[f409,f129])).
% 2.40/0.67  fof(f129,plain,(
% 2.40/0.67    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1)) ) | (~spl6_6 | ~spl6_11)),
% 2.40/0.67    inference(resolution,[],[f127,f87])).
% 2.40/0.67  fof(f87,plain,(
% 2.40/0.67    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_6),
% 2.40/0.67    inference(avatar_component_clause,[],[f86])).
% 2.40/0.67  fof(f127,plain,(
% 2.40/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,X1)) ) | ~spl6_11),
% 2.40/0.67    inference(avatar_component_clause,[],[f126])).
% 2.40/0.67  fof(f409,plain,(
% 2.40/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl6_44),
% 2.40/0.67    inference(avatar_component_clause,[],[f408])).
% 2.40/0.67  fof(f413,plain,(
% 2.40/0.67    ~spl6_44 | ~spl6_45 | ~spl6_5 | ~spl6_21),
% 2.40/0.67    inference(avatar_split_clause,[],[f401,f246,f82,f411,f408])).
% 2.40/0.67  fof(f246,plain,(
% 2.40/0.67    spl6_21 <=> ! [X1] : (~r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.40/0.67  fof(f401,plain,(
% 2.40/0.67    ~r2_hidden(sK4(sK2,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (~spl6_5 | ~spl6_21)),
% 2.40/0.67    inference(resolution,[],[f247,f83])).
% 2.40/0.67  fof(f83,plain,(
% 2.40/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 2.40/0.67    inference(avatar_component_clause,[],[f82])).
% 2.40/0.67  fof(f247,plain,(
% 2.40/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3)) | ~r2_hidden(sK1,k1_tops_1(sK0,X1))) ) | ~spl6_21),
% 2.40/0.67    inference(avatar_component_clause,[],[f246])).
% 2.40/0.67  fof(f251,plain,(
% 2.40/0.67    ~spl6_5 | ~spl6_4 | spl6_16),
% 2.40/0.67    inference(avatar_split_clause,[],[f249,f211,f78,f82])).
% 2.40/0.67  fof(f78,plain,(
% 2.40/0.67    spl6_4 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.40/0.67  fof(f249,plain,(
% 2.40/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 2.40/0.67    inference(resolution,[],[f212,f105])).
% 2.40/0.67  fof(f105,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/0.67    inference(duplicate_literal_removal,[],[f104])).
% 2.40/0.67  fof(f104,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/0.67    inference(superposition,[],[f54,f55])).
% 2.40/0.67  fof(f55,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/0.67    inference(cnf_transformation,[],[f22])).
% 2.40/0.67  fof(f22,plain,(
% 2.40/0.67    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/0.67    inference(flattening,[],[f21])).
% 2.40/0.67  fof(f21,plain,(
% 2.40/0.67    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.40/0.67    inference(ennf_transformation,[],[f4])).
% 2.40/0.67  fof(f4,axiom,(
% 2.40/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.40/0.67  fof(f54,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/0.67    inference(cnf_transformation,[],[f20])).
% 2.40/0.67  fof(f20,plain,(
% 2.40/0.67    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/0.67    inference(flattening,[],[f19])).
% 2.40/0.67  fof(f19,plain,(
% 2.40/0.67    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.40/0.67    inference(ennf_transformation,[],[f3])).
% 2.40/0.67  fof(f3,axiom,(
% 2.40/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.40/0.67  fof(f212,plain,(
% 2.40/0.67    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 2.40/0.67    inference(avatar_component_clause,[],[f211])).
% 2.40/0.67  fof(f248,plain,(
% 2.40/0.67    ~spl6_16 | spl6_21 | ~spl6_7 | spl6_17),
% 2.40/0.67    inference(avatar_split_clause,[],[f244,f214,f90,f246,f211])).
% 2.40/0.67  fof(f244,plain,(
% 2.40/0.67    ( ! [X1] : (~r2_hidden(sK1,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(X1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK2,sK3))) ) | (~spl6_7 | spl6_17)),
% 2.40/0.67    inference(resolution,[],[f220,f143])).
% 2.40/0.67  fof(f143,plain,(
% 2.40/0.67    ( ! [X0,X1] : (r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(X1,X0),X0)) ) | ~spl6_7),
% 2.40/0.67    inference(resolution,[],[f142,f53])).
% 2.40/0.67  fof(f53,plain,(
% 2.40/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f32])).
% 2.40/0.67  fof(f216,plain,(
% 2.40/0.67    ~spl6_16 | ~spl6_17 | ~spl6_6 | spl6_10 | ~spl6_13),
% 2.40/0.67    inference(avatar_split_clause,[],[f201,f196,f109,f86,f214,f211])).
% 2.40/0.67  fof(f109,plain,(
% 2.40/0.67    spl6_10 <=> m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 2.40/0.67  fof(f196,plain,(
% 2.40/0.67    spl6_13 <=> ! [X1,X0] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 2.40/0.67  fof(f201,plain,(
% 2.40/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_6 | spl6_10 | ~spl6_13)),
% 2.40/0.67    inference(resolution,[],[f199,f110])).
% 2.40/0.67  fof(f110,plain,(
% 2.40/0.67    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | spl6_10),
% 2.40/0.67    inference(avatar_component_clause,[],[f109])).
% 2.40/0.67  fof(f199,plain,(
% 2.40/0.67    ( ! [X0] : (m1_connsp_2(X0,sK0,sK1) | ~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_6 | ~spl6_13)),
% 2.40/0.67    inference(resolution,[],[f197,f87])).
% 2.40/0.67  fof(f197,plain,(
% 2.40/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_13),
% 2.40/0.67    inference(avatar_component_clause,[],[f196])).
% 2.40/0.67  fof(f198,plain,(
% 2.40/0.67    spl6_9 | ~spl6_7 | spl6_13 | ~spl6_8),
% 2.40/0.67    inference(avatar_split_clause,[],[f194,f94,f196,f90,f98])).
% 2.40/0.67  fof(f98,plain,(
% 2.40/0.67    spl6_9 <=> v2_struct_0(sK0)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.40/0.67  fof(f94,plain,(
% 2.40/0.67    spl6_8 <=> v2_pre_topc(sK0)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.40/0.67  fof(f194,plain,(
% 2.40/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | ~spl6_8),
% 2.40/0.67    inference(resolution,[],[f49,f95])).
% 2.40/0.67  fof(f95,plain,(
% 2.40/0.67    v2_pre_topc(sK0) | ~spl6_8),
% 2.40/0.67    inference(avatar_component_clause,[],[f94])).
% 2.40/0.67  fof(f49,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f28])).
% 2.40/0.67  fof(f28,plain,(
% 2.40/0.67    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.67    inference(nnf_transformation,[],[f15])).
% 2.40/0.67  fof(f15,plain,(
% 2.40/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.67    inference(flattening,[],[f14])).
% 2.40/0.67  fof(f14,plain,(
% 2.40/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.67    inference(ennf_transformation,[],[f6])).
% 2.40/0.67  fof(f6,axiom,(
% 2.40/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 2.40/0.67  fof(f128,plain,(
% 2.40/0.67    spl6_9 | ~spl6_7 | spl6_11 | ~spl6_8),
% 2.40/0.67    inference(avatar_split_clause,[],[f122,f94,f126,f90,f98])).
% 2.40/0.67  fof(f122,plain,(
% 2.40/0.67    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl6_8),
% 2.40/0.67    inference(resolution,[],[f101,f95])).
% 2.40/0.67  fof(f101,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | v2_struct_0(X0)) )),
% 2.40/0.67    inference(subsumption_resolution,[],[f48,f50])).
% 2.40/0.67  fof(f50,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f17])).
% 2.40/0.67  fof(f17,plain,(
% 2.40/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.67    inference(flattening,[],[f16])).
% 2.40/0.67  fof(f16,plain,(
% 2.40/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.67    inference(ennf_transformation,[],[f7])).
% 2.40/0.67  fof(f7,axiom,(
% 2.40/0.67    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 2.40/0.67  fof(f48,plain,(
% 2.40/0.67    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f28])).
% 2.40/0.67  fof(f111,plain,(
% 2.40/0.67    ~spl6_5 | ~spl6_4 | ~spl6_10 | spl6_1),
% 2.40/0.67    inference(avatar_split_clause,[],[f103,f66,f109,f78,f82])).
% 2.40/0.67  fof(f66,plain,(
% 2.40/0.67    spl6_1 <=> m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 2.40/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.40/0.67  fof(f103,plain,(
% 2.40/0.67    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 2.40/0.67    inference(superposition,[],[f67,f55])).
% 2.40/0.67  fof(f67,plain,(
% 2.40/0.67    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | spl6_1),
% 2.40/0.67    inference(avatar_component_clause,[],[f66])).
% 2.40/0.67  fof(f100,plain,(
% 2.40/0.67    ~spl6_9),
% 2.40/0.67    inference(avatar_split_clause,[],[f38,f98])).
% 2.40/0.67  fof(f38,plain,(
% 2.40/0.67    ~v2_struct_0(sK0)),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f27,plain,(
% 2.40/0.67    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.40/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f26,f25,f24,f23])).
% 2.40/0.67  fof(f23,plain,(
% 2.40/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f24,plain,(
% 2.40/0.67    ? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f25,plain,(
% 2.40/0.67    ? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f26,plain,(
% 2.40/0.67    ? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) & m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.40/0.67    introduced(choice_axiom,[])).
% 2.40/0.67  fof(f11,plain,(
% 2.40/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.67    inference(flattening,[],[f10])).
% 2.40/0.67  fof(f10,plain,(
% 2.40/0.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/0.67    inference(ennf_transformation,[],[f9])).
% 2.40/0.67  fof(f9,negated_conjecture,(
% 2.40/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.40/0.67    inference(negated_conjecture,[],[f8])).
% 2.40/0.67  fof(f8,conjecture,(
% 2.40/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).
% 2.40/0.67  fof(f96,plain,(
% 2.40/0.67    spl6_8),
% 2.40/0.67    inference(avatar_split_clause,[],[f39,f94])).
% 2.40/0.67  fof(f39,plain,(
% 2.40/0.67    v2_pre_topc(sK0)),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f92,plain,(
% 2.40/0.67    spl6_7),
% 2.40/0.67    inference(avatar_split_clause,[],[f40,f90])).
% 2.40/0.67  fof(f40,plain,(
% 2.40/0.67    l1_pre_topc(sK0)),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f88,plain,(
% 2.40/0.67    spl6_6),
% 2.40/0.67    inference(avatar_split_clause,[],[f41,f86])).
% 2.40/0.67  fof(f41,plain,(
% 2.40/0.67    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f84,plain,(
% 2.40/0.67    spl6_5),
% 2.40/0.67    inference(avatar_split_clause,[],[f42,f82])).
% 2.40/0.67  fof(f42,plain,(
% 2.40/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f80,plain,(
% 2.40/0.67    spl6_4),
% 2.40/0.67    inference(avatar_split_clause,[],[f43,f78])).
% 2.40/0.67  fof(f43,plain,(
% 2.40/0.67    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f76,plain,(
% 2.40/0.67    spl6_3),
% 2.40/0.67    inference(avatar_split_clause,[],[f44,f74])).
% 2.40/0.67  fof(f44,plain,(
% 2.40/0.67    m1_connsp_2(sK2,sK0,sK1)),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  fof(f68,plain,(
% 2.40/0.67    ~spl6_1),
% 2.40/0.67    inference(avatar_split_clause,[],[f46,f66])).
% 2.40/0.67  fof(f46,plain,(
% 2.40/0.67    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 2.40/0.67    inference(cnf_transformation,[],[f27])).
% 2.40/0.67  % SZS output end Proof for theBenchmark
% 2.40/0.67  % (24645)------------------------------
% 2.40/0.67  % (24645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.67  % (24645)Termination reason: Refutation
% 2.40/0.67  
% 2.40/0.67  % (24645)Memory used [KB]: 11257
% 2.40/0.67  % (24645)Time elapsed: 0.230 s
% 2.40/0.67  % (24645)------------------------------
% 2.40/0.67  % (24645)------------------------------
% 2.40/0.68  % (24625)Success in time 0.316 s
%------------------------------------------------------------------------------
