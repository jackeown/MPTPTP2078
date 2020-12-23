%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 333 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   15
%              Number of atoms          :  721 (2536 expanded)
%              Number of equality atoms :   63 ( 337 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f100,f138,f141,f143,f145,f147,f307,f397,f399,f497,f499,f618,f1314,f1323,f1412])).

fof(f1412,plain,
    ( ~ spl6_5
    | ~ spl6_23
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1409])).

fof(f1409,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_23
    | spl6_30 ),
    inference(resolution,[],[f1404,f99])).

fof(f99,plain,
    ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_5
  <=> r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1404,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | ~ spl6_5
    | ~ spl6_23
    | spl6_30 ),
    inference(resolution,[],[f1376,f838])).

fof(f838,plain,
    ( sP0(k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | ~ spl6_23 ),
    inference(superposition,[],[f74,f496])).

fof(f496,plain,
    ( u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl6_23
  <=> u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f74,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1376,plain,
    ( ! [X4,X5] :
        ( ~ sP0(k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),X5,X4)
        | ~ r2_hidden(sK4,X4) )
    | ~ spl6_5
    | ~ spl6_23
    | spl6_30 ),
    inference(resolution,[],[f1368,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f1368,plain,
    ( r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl6_5
    | ~ spl6_23
    | spl6_30 ),
    inference(resolution,[],[f1361,f608])).

fof(f608,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl6_30
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1361,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,X0)
        | r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),X0)) )
    | ~ spl6_5
    | ~ spl6_23 ),
    inference(resolution,[],[f1310,f74])).

fof(f1310,plain,
    ( ! [X2,X1] :
        ( ~ sP0(X1,u1_struct_0(sK2),X2)
        | r2_hidden(sK4,X2)
        | r2_hidden(sK4,X1) )
    | ~ spl6_5
    | ~ spl6_23 ),
    inference(resolution,[],[f1302,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1302,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl6_5
    | ~ spl6_23 ),
    inference(resolution,[],[f838,f151])).

fof(f151,plain,
    ( ! [X4,X5] :
        ( ~ sP0(X5,X4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
        | r2_hidden(sK4,X4) )
    | ~ spl6_5 ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1323,plain,
    ( spl6_2
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1321])).

fof(f1321,plain,
    ( $false
    | spl6_2
    | ~ spl6_30 ),
    inference(resolution,[],[f631,f82])).

fof(f82,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f631,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl6_30 ),
    inference(resolution,[],[f609,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f609,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f607])).

fof(f1314,plain,
    ( ~ spl6_5
    | spl6_17
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | ~ spl6_5
    | spl6_17
    | ~ spl6_23 ),
    inference(resolution,[],[f1302,f294])).

fof(f294,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl6_17
  <=> r2_hidden(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f618,plain,
    ( spl6_1
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl6_1
    | ~ spl6_17 ),
    inference(resolution,[],[f313,f78])).

fof(f78,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_1
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f313,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl6_17 ),
    inference(resolution,[],[f295,f56])).

fof(f295,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f293])).

fof(f499,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl6_6 ),
    inference(resolution,[],[f117,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ! [X4] :
          ( sK4 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
      | ! [X5] :
          ( sK4 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
    & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
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
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,X2))) )
          & ~ r1_tsep_1(sK2,X2)
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,X2))) )
        & ~ r1_tsep_1(sK2,X2)
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) )
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) )
   => ( ( ! [X4] :
            ( sK4 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        | ! [X5] :
            ( sK4 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) )
      & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,negated_conjecture,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f117,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f497,plain,
    ( spl6_23
    | spl6_4
    | ~ spl6_9
    | ~ spl6_7
    | spl6_6
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f492,f395,f115,f119,f127,f93,f494])).

fof(f93,plain,
    ( spl6_4
  <=> v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f127,plain,
    ( spl6_9
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f119,plain,
    ( spl6_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f395,plain,
    ( spl6_18
  <=> ! [X0] :
        ( v2_struct_0(k2_tsep_1(X0,sK2,sK3))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f492,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl6_18 ),
    inference(resolution,[],[f396,f46])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(k2_tsep_1(X0,sK2,sK3))
        | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f395])).

fof(f399,plain,(
    ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl6_10 ),
    inference(resolution,[],[f133,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f133,plain,
    ( v2_struct_0(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f397,plain,
    ( spl6_8
    | spl6_10
    | spl6_18 ),
    inference(avatar_split_clause,[],[f393,f395,f131,f123])).

fof(f123,plain,
    ( spl6_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f393,plain,(
    ! [X0] :
      ( v2_struct_0(k2_tsep_1(X0,sK2,sK3))
      | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f218,f47])).

fof(f47,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f193,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f307,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl6_8 ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f125,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f147,plain,
    ( spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f146,f93,f135,f131,f127,f123,f119,f115])).

fof(f135,plain,
    ( spl6_11
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f146,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f95,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,
    ( v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f145,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f137,f46])).

fof(f137,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl6_9 ),
    inference(resolution,[],[f129,f44])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f129,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f141,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f121,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f138,plain,
    ( spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_3 ),
    inference(avatar_split_clause,[],[f113,f89,f135,f131,f127,f123,f119,f115])).

fof(f89,plain,
    ( spl6_3
  <=> l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f113,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_3 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | spl6_3 ),
    inference(resolution,[],[f60,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0)
        | ~ l1_pre_topc(X0) )
    | spl6_3 ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f91,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f100,plain,
    ( ~ spl6_3
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f87,f97,f93,f89])).

fof(f87,plain,
    ( r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))
    | v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f72,f80,f76])).

fof(f72,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X5] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:39:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (7387)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.16/0.51  % (7380)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.51  % (7397)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.52  % (7381)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.52  % (7389)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (7397)Refutation not found, incomplete strategy% (7397)------------------------------
% 1.27/0.53  % (7397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (7393)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.53  % (7375)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (7377)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (7403)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.53  % (7397)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (7397)Memory used [KB]: 10746
% 1.27/0.53  % (7397)Time elapsed: 0.107 s
% 1.27/0.53  % (7397)------------------------------
% 1.27/0.53  % (7397)------------------------------
% 1.27/0.54  % (7392)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.54  % (7376)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (7394)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.54  % (7378)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.55  % (7401)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.55  % (7404)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.55  % (7399)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.55  % (7385)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.55  % (7385)Refutation not found, incomplete strategy% (7385)------------------------------
% 1.27/0.55  % (7385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (7385)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (7385)Memory used [KB]: 10746
% 1.27/0.55  % (7385)Time elapsed: 0.139 s
% 1.27/0.55  % (7385)------------------------------
% 1.27/0.55  % (7385)------------------------------
% 1.27/0.55  % (7386)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (7388)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.56  % (7395)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.56  % (7391)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.56  % (7390)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.56  % (7382)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.56  % (7402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.57  % (7386)Refutation not found, incomplete strategy% (7386)------------------------------
% 1.27/0.57  % (7386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.57  % (7384)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.57  % (7386)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.57  
% 1.27/0.57  % (7386)Memory used [KB]: 10618
% 1.27/0.57  % (7386)Time elapsed: 0.125 s
% 1.27/0.57  % (7386)------------------------------
% 1.27/0.57  % (7386)------------------------------
% 1.27/0.57  % (7398)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.57  % (7379)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.57  % (7383)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.57  % (7400)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.59  % (7396)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.62  % (7387)Refutation found. Thanks to Tanya!
% 1.27/0.62  % SZS status Theorem for theBenchmark
% 1.27/0.62  % SZS output start Proof for theBenchmark
% 1.27/0.62  fof(f1413,plain,(
% 1.27/0.62    $false),
% 1.27/0.62    inference(avatar_sat_refutation,[],[f83,f100,f138,f141,f143,f145,f147,f307,f397,f399,f497,f499,f618,f1314,f1323,f1412])).
% 1.27/0.62  fof(f1412,plain,(
% 1.27/0.62    ~spl6_5 | ~spl6_23 | spl6_30),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f1409])).
% 1.27/0.62  fof(f1409,plain,(
% 1.27/0.62    $false | (~spl6_5 | ~spl6_23 | spl6_30)),
% 1.27/0.62    inference(resolution,[],[f1404,f99])).
% 1.27/0.62  fof(f99,plain,(
% 1.27/0.62    r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) | ~spl6_5),
% 1.27/0.62    inference(avatar_component_clause,[],[f97])).
% 1.27/0.62  fof(f97,plain,(
% 1.27/0.62    spl6_5 <=> r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.27/0.62  fof(f1404,plain,(
% 1.27/0.62    ~r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) | (~spl6_5 | ~spl6_23 | spl6_30)),
% 1.27/0.62    inference(resolution,[],[f1376,f838])).
% 1.27/0.62  fof(f838,plain,(
% 1.27/0.62    sP0(k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK2),u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) | ~spl6_23),
% 1.27/0.62    inference(superposition,[],[f74,f496])).
% 1.27/0.62  fof(f496,plain,(
% 1.27/0.62    u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) | ~spl6_23),
% 1.27/0.62    inference(avatar_component_clause,[],[f494])).
% 1.27/0.62  fof(f494,plain,(
% 1.27/0.62    spl6_23 <=> u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.27/0.62  fof(f74,plain,(
% 1.27/0.62    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.27/0.62    inference(equality_resolution,[],[f67])).
% 1.27/0.62  fof(f67,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.27/0.62    inference(cnf_transformation,[],[f39])).
% 1.27/0.62  fof(f39,plain,(
% 1.27/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.27/0.62    inference(nnf_transformation,[],[f27])).
% 1.27/0.62  fof(f27,plain,(
% 1.27/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.27/0.62    inference(definition_folding,[],[f1,f26])).
% 1.27/0.62  fof(f26,plain,(
% 1.27/0.62    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.27/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.27/0.62  fof(f1,axiom,(
% 1.27/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.27/0.62  fof(f1376,plain,(
% 1.27/0.62    ( ! [X4,X5] : (~sP0(k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),X5,X4) | ~r2_hidden(sK4,X4)) ) | (~spl6_5 | ~spl6_23 | spl6_30)),
% 1.27/0.62    inference(resolution,[],[f1368,f62])).
% 1.27/0.62  fof(f62,plain,(
% 1.27/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f38])).
% 1.27/0.62  fof(f38,plain,(
% 1.27/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.27/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 1.27/0.62  fof(f37,plain,(
% 1.27/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.27/0.62    introduced(choice_axiom,[])).
% 1.27/0.62  fof(f36,plain,(
% 1.27/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.27/0.62    inference(rectify,[],[f35])).
% 1.27/0.62  fof(f35,plain,(
% 1.27/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.27/0.62    inference(flattening,[],[f34])).
% 1.27/0.62  fof(f34,plain,(
% 1.27/0.62    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.27/0.62    inference(nnf_transformation,[],[f26])).
% 1.27/0.62  fof(f1368,plain,(
% 1.27/0.62    r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) | (~spl6_5 | ~spl6_23 | spl6_30)),
% 1.27/0.62    inference(resolution,[],[f1361,f608])).
% 1.27/0.62  fof(f608,plain,(
% 1.27/0.62    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl6_30),
% 1.27/0.62    inference(avatar_component_clause,[],[f607])).
% 1.27/0.62  fof(f607,plain,(
% 1.27/0.62    spl6_30 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.27/0.62  fof(f1361,plain,(
% 1.27/0.62    ( ! [X0] : (r2_hidden(sK4,X0) | r2_hidden(sK4,k4_xboole_0(u1_struct_0(sK2),X0))) ) | (~spl6_5 | ~spl6_23)),
% 1.27/0.62    inference(resolution,[],[f1310,f74])).
% 1.27/0.62  fof(f1310,plain,(
% 1.27/0.62    ( ! [X2,X1] : (~sP0(X1,u1_struct_0(sK2),X2) | r2_hidden(sK4,X2) | r2_hidden(sK4,X1)) ) | (~spl6_5 | ~spl6_23)),
% 1.27/0.62    inference(resolution,[],[f1302,f63])).
% 1.27/0.62  fof(f63,plain,(
% 1.27/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f38])).
% 1.27/0.62  fof(f1302,plain,(
% 1.27/0.62    r2_hidden(sK4,u1_struct_0(sK2)) | (~spl6_5 | ~spl6_23)),
% 1.27/0.62    inference(resolution,[],[f838,f151])).
% 1.27/0.62  fof(f151,plain,(
% 1.27/0.62    ( ! [X4,X5] : (~sP0(X5,X4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) | r2_hidden(sK4,X4)) ) | ~spl6_5),
% 1.27/0.62    inference(resolution,[],[f99,f61])).
% 1.27/0.62  fof(f61,plain,(
% 1.27/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f38])).
% 1.27/0.62  fof(f1323,plain,(
% 1.27/0.62    spl6_2 | ~spl6_30),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f1321])).
% 1.27/0.62  fof(f1321,plain,(
% 1.27/0.62    $false | (spl6_2 | ~spl6_30)),
% 1.27/0.62    inference(resolution,[],[f631,f82])).
% 1.27/0.62  fof(f82,plain,(
% 1.27/0.62    ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl6_2),
% 1.27/0.62    inference(avatar_component_clause,[],[f80])).
% 1.27/0.62  fof(f80,plain,(
% 1.27/0.62    spl6_2 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.27/0.62  fof(f631,plain,(
% 1.27/0.62    m1_subset_1(sK4,u1_struct_0(sK3)) | ~spl6_30),
% 1.27/0.62    inference(resolution,[],[f609,f56])).
% 1.27/0.62  fof(f56,plain,(
% 1.27/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f21])).
% 1.27/0.62  fof(f21,plain,(
% 1.27/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.27/0.62    inference(ennf_transformation,[],[f3])).
% 1.27/0.62  fof(f3,axiom,(
% 1.27/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.27/0.62  fof(f609,plain,(
% 1.27/0.62    r2_hidden(sK4,u1_struct_0(sK3)) | ~spl6_30),
% 1.27/0.62    inference(avatar_component_clause,[],[f607])).
% 1.27/0.62  fof(f1314,plain,(
% 1.27/0.62    ~spl6_5 | spl6_17 | ~spl6_23),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f1307])).
% 1.27/0.62  fof(f1307,plain,(
% 1.27/0.62    $false | (~spl6_5 | spl6_17 | ~spl6_23)),
% 1.27/0.62    inference(resolution,[],[f1302,f294])).
% 1.27/0.62  fof(f294,plain,(
% 1.27/0.62    ~r2_hidden(sK4,u1_struct_0(sK2)) | spl6_17),
% 1.27/0.62    inference(avatar_component_clause,[],[f293])).
% 1.27/0.62  fof(f293,plain,(
% 1.27/0.62    spl6_17 <=> r2_hidden(sK4,u1_struct_0(sK2))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.27/0.62  fof(f618,plain,(
% 1.27/0.62    spl6_1 | ~spl6_17),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f616])).
% 1.27/0.62  fof(f616,plain,(
% 1.27/0.62    $false | (spl6_1 | ~spl6_17)),
% 1.27/0.62    inference(resolution,[],[f313,f78])).
% 1.27/0.62  fof(f78,plain,(
% 1.27/0.62    ~m1_subset_1(sK4,u1_struct_0(sK2)) | spl6_1),
% 1.27/0.62    inference(avatar_component_clause,[],[f76])).
% 1.27/0.62  fof(f76,plain,(
% 1.27/0.62    spl6_1 <=> m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.27/0.62  fof(f313,plain,(
% 1.27/0.62    m1_subset_1(sK4,u1_struct_0(sK2)) | ~spl6_17),
% 1.27/0.62    inference(resolution,[],[f295,f56])).
% 1.27/0.62  fof(f295,plain,(
% 1.27/0.62    r2_hidden(sK4,u1_struct_0(sK2)) | ~spl6_17),
% 1.27/0.62    inference(avatar_component_clause,[],[f293])).
% 1.27/0.62  fof(f499,plain,(
% 1.27/0.62    ~spl6_6),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f498])).
% 1.27/0.62  fof(f498,plain,(
% 1.27/0.62    $false | ~spl6_6),
% 1.27/0.62    inference(resolution,[],[f117,f40])).
% 1.27/0.62  fof(f40,plain,(
% 1.27/0.62    ~v2_struct_0(sK1)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f32,plain,(
% 1.27/0.62    ((((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.27/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f31,f30,f29,f28])).
% 1.27/0.62  fof(f28,plain,(
% 1.27/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.27/0.62    introduced(choice_axiom,[])).
% 1.27/0.62  fof(f29,plain,(
% 1.27/0.62    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,X2)))) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.27/0.62    introduced(choice_axiom,[])).
% 1.27/0.62  fof(f30,plain,(
% 1.27/0.62    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,X2)))) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.27/0.62    introduced(choice_axiom,[])).
% 1.27/0.62  fof(f31,plain,(
% 1.27/0.62    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))) => ((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) | ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2)))) & m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))))),
% 1.27/0.62    introduced(choice_axiom,[])).
% 1.27/0.62  fof(f14,plain,(
% 1.27/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.62    inference(flattening,[],[f13])).
% 1.27/0.62  fof(f13,plain,(
% 1.27/0.62    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.62    inference(ennf_transformation,[],[f12])).
% 1.27/0.62  fof(f12,plain,(
% 1.27/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.27/0.62    inference(rectify,[],[f11])).
% 1.27/0.62  fof(f11,negated_conjecture,(
% 1.27/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.27/0.62    inference(negated_conjecture,[],[f10])).
% 1.27/0.62  fof(f10,conjecture,(
% 1.27/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.27/0.62  fof(f117,plain,(
% 1.27/0.62    v2_struct_0(sK1) | ~spl6_6),
% 1.27/0.62    inference(avatar_component_clause,[],[f115])).
% 1.27/0.62  fof(f115,plain,(
% 1.27/0.62    spl6_6 <=> v2_struct_0(sK1)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.27/0.62  fof(f497,plain,(
% 1.27/0.62    spl6_23 | spl6_4 | ~spl6_9 | ~spl6_7 | spl6_6 | ~spl6_18),
% 1.27/0.62    inference(avatar_split_clause,[],[f492,f395,f115,f119,f127,f93,f494])).
% 1.27/0.62  fof(f93,plain,(
% 1.27/0.62    spl6_4 <=> v2_struct_0(k2_tsep_1(sK1,sK2,sK3))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.27/0.62  fof(f127,plain,(
% 1.27/0.62    spl6_9 <=> m1_pre_topc(sK2,sK1)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.27/0.62  fof(f119,plain,(
% 1.27/0.62    spl6_7 <=> l1_pre_topc(sK1)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.27/0.62  fof(f395,plain,(
% 1.27/0.62    spl6_18 <=> ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK2,sK3)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK3,X0) | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.27/0.62  fof(f492,plain,(
% 1.27/0.62    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) | u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) | ~spl6_18),
% 1.27/0.62    inference(resolution,[],[f396,f46])).
% 1.27/0.62  fof(f46,plain,(
% 1.27/0.62    m1_pre_topc(sK3,sK1)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f396,plain,(
% 1.27/0.62    ( ! [X0] : (~m1_pre_topc(sK3,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(k2_tsep_1(X0,sK2,sK3)) | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))) ) | ~spl6_18),
% 1.27/0.62    inference(avatar_component_clause,[],[f395])).
% 1.27/0.62  fof(f399,plain,(
% 1.27/0.62    ~spl6_10),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f398])).
% 1.27/0.62  fof(f398,plain,(
% 1.27/0.62    $false | ~spl6_10),
% 1.27/0.62    inference(resolution,[],[f133,f45])).
% 1.27/0.62  fof(f45,plain,(
% 1.27/0.62    ~v2_struct_0(sK3)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f133,plain,(
% 1.27/0.62    v2_struct_0(sK3) | ~spl6_10),
% 1.27/0.62    inference(avatar_component_clause,[],[f131])).
% 1.27/0.62  fof(f131,plain,(
% 1.27/0.62    spl6_10 <=> v2_struct_0(sK3)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.27/0.62  fof(f397,plain,(
% 1.27/0.62    spl6_8 | spl6_10 | spl6_18),
% 1.27/0.62    inference(avatar_split_clause,[],[f393,f395,f131,f123])).
% 1.27/0.62  fof(f123,plain,(
% 1.27/0.62    spl6_8 <=> v2_struct_0(sK2)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.27/0.62  fof(f393,plain,(
% 1.27/0.62    ( ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK2,sK3)) | u1_struct_0(k2_tsep_1(X0,sK2,sK3)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(resolution,[],[f218,f47])).
% 1.27/0.62  fof(f47,plain,(
% 1.27/0.62    ~r1_tsep_1(sK2,sK3)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f218,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(duplicate_literal_removal,[],[f217])).
% 1.27/0.62  fof(f217,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(resolution,[],[f193,f60])).
% 1.27/0.62  fof(f60,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f25])).
% 1.27/0.62  fof(f25,plain,(
% 1.27/0.62    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.62    inference(flattening,[],[f24])).
% 1.27/0.62  fof(f24,plain,(
% 1.27/0.62    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.62    inference(ennf_transformation,[],[f9])).
% 1.27/0.62  fof(f9,axiom,(
% 1.27/0.62    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.27/0.62  fof(f193,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(duplicate_literal_removal,[],[f192])).
% 1.27/0.62  fof(f192,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(resolution,[],[f73,f59])).
% 1.27/0.62  fof(f59,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f25])).
% 1.27/0.62  fof(f73,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(equality_resolution,[],[f70])).
% 1.27/0.62  fof(f70,plain,(
% 1.27/0.62    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(definition_unfolding,[],[f53,f55])).
% 1.27/0.62  fof(f55,plain,(
% 1.27/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f2])).
% 1.27/0.62  fof(f2,axiom,(
% 1.27/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.27/0.62  fof(f53,plain,(
% 1.27/0.62    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f33])).
% 1.27/0.62  fof(f33,plain,(
% 1.27/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.62    inference(nnf_transformation,[],[f20])).
% 1.27/0.62  fof(f20,plain,(
% 1.27/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.62    inference(flattening,[],[f19])).
% 1.27/0.62  fof(f19,plain,(
% 1.27/0.62    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.62    inference(ennf_transformation,[],[f8])).
% 1.27/0.62  fof(f8,axiom,(
% 1.27/0.62    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.27/0.62  fof(f307,plain,(
% 1.27/0.62    ~spl6_8),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f306])).
% 1.27/0.62  fof(f306,plain,(
% 1.27/0.62    $false | ~spl6_8),
% 1.27/0.62    inference(resolution,[],[f125,f43])).
% 1.27/0.62  fof(f43,plain,(
% 1.27/0.62    ~v2_struct_0(sK2)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f125,plain,(
% 1.27/0.62    v2_struct_0(sK2) | ~spl6_8),
% 1.27/0.62    inference(avatar_component_clause,[],[f123])).
% 1.27/0.62  fof(f147,plain,(
% 1.27/0.62    spl6_6 | ~spl6_7 | spl6_8 | ~spl6_9 | spl6_10 | ~spl6_11 | ~spl6_4),
% 1.27/0.62    inference(avatar_split_clause,[],[f146,f93,f135,f131,f127,f123,f119,f115])).
% 1.27/0.62  fof(f135,plain,(
% 1.27/0.62    spl6_11 <=> m1_pre_topc(sK3,sK1)),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.27/0.62  fof(f146,plain,(
% 1.27/0.62    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl6_4),
% 1.27/0.62    inference(resolution,[],[f95,f58])).
% 1.27/0.62  fof(f58,plain,(
% 1.27/0.62    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f25])).
% 1.27/0.62  fof(f95,plain,(
% 1.27/0.62    v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) | ~spl6_4),
% 1.27/0.62    inference(avatar_component_clause,[],[f93])).
% 1.27/0.62  fof(f145,plain,(
% 1.27/0.62    spl6_11),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f144])).
% 1.27/0.62  fof(f144,plain,(
% 1.27/0.62    $false | spl6_11),
% 1.27/0.62    inference(resolution,[],[f137,f46])).
% 1.27/0.62  fof(f137,plain,(
% 1.27/0.62    ~m1_pre_topc(sK3,sK1) | spl6_11),
% 1.27/0.62    inference(avatar_component_clause,[],[f135])).
% 1.27/0.62  fof(f143,plain,(
% 1.27/0.62    spl6_9),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f142])).
% 1.27/0.62  fof(f142,plain,(
% 1.27/0.62    $false | spl6_9),
% 1.27/0.62    inference(resolution,[],[f129,f44])).
% 1.27/0.62  fof(f44,plain,(
% 1.27/0.62    m1_pre_topc(sK2,sK1)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f129,plain,(
% 1.27/0.62    ~m1_pre_topc(sK2,sK1) | spl6_9),
% 1.27/0.62    inference(avatar_component_clause,[],[f127])).
% 1.27/0.62  fof(f141,plain,(
% 1.27/0.62    spl6_7),
% 1.27/0.62    inference(avatar_contradiction_clause,[],[f139])).
% 1.27/0.62  fof(f139,plain,(
% 1.27/0.62    $false | spl6_7),
% 1.27/0.62    inference(resolution,[],[f121,f42])).
% 1.27/0.62  fof(f42,plain,(
% 1.27/0.62    l1_pre_topc(sK1)),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f121,plain,(
% 1.27/0.62    ~l1_pre_topc(sK1) | spl6_7),
% 1.27/0.62    inference(avatar_component_clause,[],[f119])).
% 1.27/0.62  fof(f138,plain,(
% 1.27/0.62    spl6_6 | ~spl6_7 | spl6_8 | ~spl6_9 | spl6_10 | ~spl6_11 | spl6_3),
% 1.27/0.62    inference(avatar_split_clause,[],[f113,f89,f135,f131,f127,f123,f119,f115])).
% 1.27/0.62  fof(f89,plain,(
% 1.27/0.62    spl6_3 <=> l1_pre_topc(k2_tsep_1(sK1,sK2,sK3))),
% 1.27/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.27/0.62  fof(f113,plain,(
% 1.27/0.62    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | spl6_3),
% 1.27/0.62    inference(duplicate_literal_removal,[],[f112])).
% 1.27/0.62  fof(f112,plain,(
% 1.27/0.62    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | spl6_3),
% 1.27/0.62    inference(resolution,[],[f60,f101])).
% 1.27/0.62  fof(f101,plain,(
% 1.27/0.62    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X0) | ~l1_pre_topc(X0)) ) | spl6_3),
% 1.27/0.62    inference(resolution,[],[f91,f51])).
% 1.27/0.62  fof(f51,plain,(
% 1.27/0.62    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f16])).
% 1.27/0.62  fof(f16,plain,(
% 1.27/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.27/0.62    inference(ennf_transformation,[],[f6])).
% 1.27/0.62  fof(f6,axiom,(
% 1.27/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.27/0.62  fof(f91,plain,(
% 1.27/0.62    ~l1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) | spl6_3),
% 1.27/0.62    inference(avatar_component_clause,[],[f89])).
% 1.27/0.62  fof(f100,plain,(
% 1.27/0.62    ~spl6_3 | spl6_4 | spl6_5),
% 1.27/0.62    inference(avatar_split_clause,[],[f87,f97,f93,f89])).
% 1.27/0.62  fof(f87,plain,(
% 1.27/0.62    r2_hidden(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3))) | v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) | ~l1_pre_topc(k2_tsep_1(sK1,sK2,sK3))),
% 1.27/0.62    inference(resolution,[],[f86,f48])).
% 1.27/0.62  fof(f48,plain,(
% 1.27/0.62    m1_subset_1(sK4,u1_struct_0(k2_tsep_1(sK1,sK2,sK3)))),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  fof(f86,plain,(
% 1.27/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1)) )),
% 1.27/0.62    inference(resolution,[],[f84,f50])).
% 1.27/0.62  fof(f50,plain,(
% 1.27/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f15])).
% 1.27/0.62  fof(f15,plain,(
% 1.27/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.27/0.62    inference(ennf_transformation,[],[f5])).
% 1.27/0.62  fof(f5,axiom,(
% 1.27/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.27/0.62  fof(f84,plain,(
% 1.27/0.62    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 1.27/0.62    inference(resolution,[],[f57,f52])).
% 1.27/0.62  fof(f52,plain,(
% 1.27/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f18])).
% 1.27/0.62  fof(f18,plain,(
% 1.27/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.27/0.62    inference(flattening,[],[f17])).
% 1.27/0.62  fof(f17,plain,(
% 1.27/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.27/0.62    inference(ennf_transformation,[],[f7])).
% 1.27/0.62  fof(f7,axiom,(
% 1.27/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.27/0.62  fof(f57,plain,(
% 1.27/0.62    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.27/0.62    inference(cnf_transformation,[],[f23])).
% 1.27/0.62  fof(f23,plain,(
% 1.27/0.62    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.27/0.62    inference(flattening,[],[f22])).
% 1.27/0.62  fof(f22,plain,(
% 1.27/0.62    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.27/0.62    inference(ennf_transformation,[],[f4])).
% 1.27/0.62  fof(f4,axiom,(
% 1.27/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.27/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.27/0.62  fof(f83,plain,(
% 1.27/0.62    ~spl6_1 | ~spl6_2),
% 1.27/0.62    inference(avatar_split_clause,[],[f72,f80,f76])).
% 1.27/0.62  fof(f72,plain,(
% 1.27/0.62    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.27/0.62    inference(equality_resolution,[],[f71])).
% 1.27/0.62  fof(f71,plain,(
% 1.27/0.62    ( ! [X5] : (~m1_subset_1(sK4,u1_struct_0(sK3)) | sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 1.27/0.62    inference(equality_resolution,[],[f49])).
% 1.27/0.62  fof(f49,plain,(
% 1.27/0.62    ( ! [X4,X5] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3)) | sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 1.27/0.62    inference(cnf_transformation,[],[f32])).
% 1.27/0.62  % SZS output end Proof for theBenchmark
% 1.27/0.62  % (7387)------------------------------
% 1.27/0.62  % (7387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.62  % (7387)Termination reason: Refutation
% 1.27/0.62  
% 1.27/0.62  % (7387)Memory used [KB]: 6908
% 1.27/0.62  % (7387)Time elapsed: 0.211 s
% 1.27/0.62  % (7387)------------------------------
% 1.27/0.62  % (7387)------------------------------
% 1.94/0.65  % (7374)Success in time 0.278 s
%------------------------------------------------------------------------------
