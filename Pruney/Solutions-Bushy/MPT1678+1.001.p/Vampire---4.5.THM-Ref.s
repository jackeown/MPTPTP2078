%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1678+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  326 (2103 expanded)
%              Number of leaves         :   38 ( 744 expanded)
%              Depth                    :   31
%              Number of atoms          : 2228 (37499 expanded)
%              Number of equality atoms :   82 (4688 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f93,f178,f193,f209,f220,f232,f294,f303,f326,f345,f359,f361,f443,f459,f462,f470,f480,f502,f534,f562,f568,f597,f610,f696,f736,f772])).

fof(f772,plain,
    ( ~ spl11_13
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f767,f205])).

fof(f205,plain,
    ( sP1(sK4,sK2,sK3)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl11_13
  <=> sP1(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f767,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | ~ spl11_15 ),
    inference(resolution,[],[f215,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
     => ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f215,plain,
    ( r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl11_15
  <=> r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f736,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f734,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r2_yellow_0(sK2,sK4)
      | ~ r2_yellow_0(sK2,sK3) )
    & ( r2_yellow_0(sK2,sK4)
      | r2_yellow_0(sK2,sK3) )
    & ! [X3] :
        ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3) )
    & ! [X4] :
        ( ( k2_yellow_0(sK2,sK5(X4)) = X4
          & r2_yellow_0(sK2,sK5(X4))
          & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
          & v1_finset_1(sK5(X4)) )
        | ~ r2_hidden(X4,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & ! [X6] :
        ( r2_yellow_0(sK2,X6)
        | k1_xboole_0 = X6
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X6) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_yellow_0(X0,X2)
                  | ~ r2_yellow_0(X0,X1) )
                & ( r2_yellow_0(X0,X2)
                  | r2_yellow_0(X0,X1) )
                & ! [X3] :
                    ( r2_hidden(k2_yellow_0(X0,X3),X2)
                    | k1_xboole_0 = X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X3) )
                & ! [X4] :
                    ( ? [X5] :
                        ( k2_yellow_0(X0,X5) = X4
                        & r2_yellow_0(X0,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(X1))
                        & v1_finset_1(X5) )
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & ! [X6] :
                    ( r2_yellow_0(X0,X6)
                    | k1_xboole_0 = X6
                    | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X6) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(sK2,X2)
                | ~ r2_yellow_0(sK2,X1) )
              & ( r2_yellow_0(sK2,X2)
                | r2_yellow_0(sK2,X1) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(sK2,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(sK2,X5) = X4
                      & r2_yellow_0(sK2,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
              & ! [X6] :
                  ( r2_yellow_0(sK2,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_yellow_0(sK2,X2)
              | ~ r2_yellow_0(sK2,X1) )
            & ( r2_yellow_0(sK2,X2)
              | r2_yellow_0(sK2,X1) )
            & ! [X3] :
                ( r2_hidden(k2_yellow_0(sK2,X3),X2)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            & ! [X4] :
                ( ? [X5] :
                    ( k2_yellow_0(sK2,X5) = X4
                    & r2_yellow_0(sK2,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(X1))
                    & v1_finset_1(X5) )
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            & ! [X6] :
                ( r2_yellow_0(sK2,X6)
                | k1_xboole_0 = X6
                | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ( ~ r2_yellow_0(sK2,X2)
            | ~ r2_yellow_0(sK2,sK3) )
          & ( r2_yellow_0(sK2,X2)
            | r2_yellow_0(sK2,sK3) )
          & ! [X3] :
              ( r2_hidden(k2_yellow_0(sK2,X3),X2)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X3) )
          & ! [X4] :
              ( ? [X5] :
                  ( k2_yellow_0(sK2,X5) = X4
                  & r2_yellow_0(sK2,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(sK3))
                  & v1_finset_1(X5) )
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & ! [X6] :
              ( r2_yellow_0(sK2,X6)
              | k1_xboole_0 = X6
              | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
              | ~ v1_finset_1(X6) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ~ r2_yellow_0(sK2,X2)
          | ~ r2_yellow_0(sK2,sK3) )
        & ( r2_yellow_0(sK2,X2)
          | r2_yellow_0(sK2,sK3) )
        & ! [X3] :
            ( r2_hidden(k2_yellow_0(sK2,X3),X2)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X3) )
        & ! [X4] :
            ( ? [X5] :
                ( k2_yellow_0(sK2,X5) = X4
                & r2_yellow_0(sK2,X5)
                & m1_subset_1(X5,k1_zfmisc_1(sK3))
                & v1_finset_1(X5) )
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & ! [X6] :
            ( r2_yellow_0(sK2,X6)
            | k1_xboole_0 = X6
            | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
            | ~ v1_finset_1(X6) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ r2_yellow_0(sK2,sK4)
        | ~ r2_yellow_0(sK2,sK3) )
      & ( r2_yellow_0(sK2,sK4)
        | r2_yellow_0(sK2,sK3) )
      & ! [X3] :
          ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X3) )
      & ! [X4] :
          ( ? [X5] :
              ( k2_yellow_0(sK2,X5) = X4
              & r2_yellow_0(sK2,X5)
              & m1_subset_1(X5,k1_zfmisc_1(sK3))
              & v1_finset_1(X5) )
          | ~ r2_hidden(X4,sK4)
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & ! [X6] :
          ( r2_yellow_0(sK2,X6)
          | k1_xboole_0 = X6
          | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
          | ~ v1_finset_1(X6) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4] :
      ( ? [X5] :
          ( k2_yellow_0(sK2,X5) = X4
          & r2_yellow_0(sK2,X5)
          & m1_subset_1(X5,k1_zfmisc_1(sK3))
          & v1_finset_1(X5) )
     => ( k2_yellow_0(sK2,sK5(X4)) = X4
        & r2_yellow_0(sK2,sK5(X4))
        & m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
        & v1_finset_1(sK5(X4)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X0,X2)
                | ~ r2_yellow_0(X0,X1) )
              & ( r2_yellow_0(X0,X2)
                | r2_yellow_0(X0,X1) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X0,X2)
                | ~ r2_yellow_0(X0,X1) )
              & ( r2_yellow_0(X0,X2)
                | r2_yellow_0(X0,X1) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_yellow_0(X0,X1)
              <~> r2_yellow_0(X0,X2) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_yellow_0(X0,X1)
              <~> r2_yellow_0(X0,X2) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ( r2_yellow_0(X0,X1)
                  <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => ( r2_yellow_0(X0,X1)
                  <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ( r2_yellow_0(X0,X1)
                <=> r2_yellow_0(X0,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_waybel_0)).

fof(f734,plain,
    ( v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f733,f46])).

fof(f46,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f733,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f732,f170])).

fof(f170,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl11_8
  <=> r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f732,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f731,f87])).

fof(f87,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl11_1
  <=> r2_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f731,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f720,f90])).

fof(f90,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_2
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f720,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(resolution,[],[f715,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f715,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f714,f204])).

fof(f204,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | spl11_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f714,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10
    | spl11_12 ),
    inference(subsumption_resolution,[],[f713,f200])).

fof(f200,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | spl11_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl11_12
  <=> r2_hidden(sK8(sK2,sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f713,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8
    | spl11_10 ),
    inference(subsumption_resolution,[],[f709,f176])).

fof(f176,plain,
    ( ~ sP0(sK2,sK3)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_10
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f709,plain,
    ( sP0(sK2,sK3)
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(resolution,[],[f704,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f704,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP0(sK2,X3)
        | r2_hidden(sK8(sK2,X3,sK4),sK4)
        | r1_lattice3(sK2,X3,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X3) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f703,f87])).

fof(f703,plain,
    ( ! [X3] :
        ( r2_hidden(sK8(sK2,X3,sK4),sK4)
        | sP0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X3,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X3)
        | r2_yellow_0(sK2,sK3) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f700,f48])).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f700,plain,
    ( ! [X3] :
        ( r2_hidden(sK8(sK2,X3,sK4),sK4)
        | sP0(sK2,X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X3,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X3)
        | r2_yellow_0(sK2,sK3) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(resolution,[],[f170,f550])).

fof(f550,plain,
    ( ! [X8,X7,X9] :
        ( ~ r1_lattice3(sK2,X7,sK9(sK2,sK4,X9))
        | r2_hidden(sK8(sK2,X8,X7),X7)
        | sP0(sK2,X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X8,sK9(sK2,sK4,X9))
        | sP1(X7,sK2,X8)
        | r2_yellow_0(sK2,X9) )
    | ~ spl11_2 ),
    inference(resolution,[],[f90,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | sP1(X0,sK2,X3)
      | r2_hidden(sK8(sK2,X3,X0),X0)
      | sP0(sK2,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | r2_yellow_0(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f122,f43])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | sP1(X0,sK2,X3)
      | r2_hidden(sK8(sK2,X3,X0),X0)
      | sP0(sK2,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | sP1(X0,sK2,X3)
      | r2_hidden(sK8(sK2,X3,X0),X0)
      | sP0(sK2,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,X2)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f120,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f46])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r2_hidden(sK8(sK2,X2,X0),X0)
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ( ! [X5] :
                    ( k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
                    | ~ r2_yellow_0(X0,X5)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X5) )
                & r2_hidden(sK8(X0,X1,X2),X2)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k2_yellow_0(X0,X5) != X4
              | ~ r2_yellow_0(X0,X5)
              | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X5) )
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
            | ~ r2_yellow_0(X0,X5)
            | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X5) )
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_lattice3(X0,X1,X3)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( ( r1_lattice3(X0,X1,X7)
                      | ~ r1_lattice3(X0,X2,X7) )
                    & ( r1_lattice3(X0,X2,X7)
                      | ~ r1_lattice3(X0,X1,X7) ) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | sP1(X2,X0,X1)
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <=> r1_lattice3(X0,X2,X7) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ? [X3] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
                  & k1_xboole_0 != X3
                  & m1_subset_1(X3,k1_zfmisc_1(X1))
                  & v1_finset_1(X3) )
              | ? [X4] :
                  ( ! [X5] :
                      ( k2_yellow_0(X0,X5) != X4
                      | ~ r2_yellow_0(X0,X5)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
                      | ~ v1_finset_1(X5) )
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ? [X6] :
                  ( ~ r2_yellow_0(X0,X6)
                  & k1_xboole_0 != X6
                  & m1_subset_1(X6,k1_zfmisc_1(X1))
                  & v1_finset_1(X6) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                & v1_finset_1(X5) )
                             => ~ ( k2_yellow_0(X0,X5) = X4
                                  & r2_yellow_0(X0,X5) ) )
                          & r2_hidden(X4,X2) ) )
                  & ! [X6] :
                      ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                     => ( k1_xboole_0 != X6
                       => r2_yellow_0(X0,X6) ) ) )
               => ! [X7] :
                    ( m1_subset_1(X7,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X7)
                    <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f696,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f694,f43])).

fof(f694,plain,
    ( v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f693,f46])).

fof(f693,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f692,f637])).

fof(f637,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ spl11_9
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f633,f200])).

fof(f633,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl11_9
    | spl11_13 ),
    inference(subsumption_resolution,[],[f630,f204])).

fof(f630,plain,
    ( sP1(sK4,sK2,sK3)
    | r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl11_9 ),
    inference(resolution,[],[f173,f48])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,X0,sK9(sK2,sK4,sK3))
        | r2_hidden(sK8(sK2,sK3,X0),X0) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl11_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,X0,sK9(sK2,sK4,sK3))
        | r2_hidden(sK8(sK2,sK3,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f692,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f691,f87])).

fof(f691,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f683,f90])).

fof(f683,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(resolution,[],[f678,f74])).

fof(f678,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f677,f204])).

fof(f677,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f676,f200])).

fof(f676,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_10
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f672,f176])).

fof(f672,plain,
    ( sP0(sK2,sK3)
    | r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | sP1(sK4,sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_12
    | spl11_13 ),
    inference(resolution,[],[f643,f47])).

fof(f643,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP0(sK2,X1)
        | r2_hidden(sK8(sK2,X1,sK4),sK4)
        | r1_lattice3(sK2,X1,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X1) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_9
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f642,f87])).

fof(f642,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK2,X1,sK4),sK4)
        | sP0(sK2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X1)
        | r2_yellow_0(sK2,sK3) )
    | ~ spl11_2
    | ~ spl11_9
    | spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f641,f48])).

fof(f641,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK2,X1,sK4),sK4)
        | sP0(sK2,X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK4,sK3))
        | sP1(sK4,sK2,X1)
        | r2_yellow_0(sK2,sK3) )
    | ~ spl11_2
    | ~ spl11_9
    | spl11_12
    | spl11_13 ),
    inference(resolution,[],[f637,f550])).

fof(f610,plain,
    ( spl11_1
    | ~ spl11_2
    | spl11_8
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | spl11_8
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f608,f87])).

fof(f608,plain,
    ( r2_yellow_0(sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | spl11_8
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f605,f169])).

fof(f169,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f605,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | r2_yellow_0(sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | spl11_8
    | ~ spl11_21 ),
    inference(resolution,[],[f604,f547])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,X0))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,X0))
        | r2_yellow_0(sK2,X0) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(resolution,[],[f90,f514])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,sK4,sK9(sK2,X0,X1))
        | ~ r1_lattice3(sK2,sK3,sK9(sK2,X0,X1))
        | r2_yellow_0(sK2,X1) )
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f513,f43])).

fof(f513,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,sK3,sK9(sK2,X0,X1))
        | r1_lattice3(sK2,sK4,sK9(sK2,X0,X1))
        | ~ r2_yellow_0(sK2,X0)
        | r2_yellow_0(sK2,X1)
        | v2_struct_0(sK2) )
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f511,f46])).

fof(f511,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,sK3,sK9(sK2,X0,X1))
        | r1_lattice3(sK2,sK4,sK9(sK2,X0,X1))
        | ~ r2_yellow_0(sK2,X0)
        | r2_yellow_0(sK2,X1)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_21 ),
    inference(resolution,[],[f318,f72])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK3,X0)
        | r1_lattice3(sK2,sK4,X0) )
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl11_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK3,X0)
        | r1_lattice3(sK2,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f604,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | spl11_1
    | ~ spl11_2
    | spl11_8 ),
    inference(subsumption_resolution,[],[f603,f87])).

fof(f603,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | r2_yellow_0(sK2,sK3)
    | ~ spl11_2
    | spl11_8 ),
    inference(resolution,[],[f169,f552])).

fof(f552,plain,
    ( ! [X13] :
        ( r1_lattice3(sK2,X13,sK9(sK2,sK4,X13))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,X13))
        | r2_yellow_0(sK2,X13) )
    | ~ spl11_2 ),
    inference(resolution,[],[f90,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X1,sK9(sK2,X0,X1))
      | r1_lattice3(sK2,X0,sK9(sK2,X0,X1))
      | r2_yellow_0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X1,sK9(sK2,X0,X1))
      | r1_lattice3(sK2,X0,sK9(sK2,X0,X1))
      | r2_yellow_0(sK2,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f73,f46])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f597,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_21
    | ~ spl11_42 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_21
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f595,f87])).

fof(f595,plain,
    ( r2_yellow_0(sK2,sK3)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_21
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f593,f577])).

fof(f577,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f576,f43])).

fof(f576,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f571,f46])).

fof(f571,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f570,f87])).

fof(f570,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f569,f90])).

fof(f569,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_42 ),
    inference(resolution,[],[f557,f74])).

fof(f557,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl11_42
  <=> r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f593,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | r2_yellow_0(sK2,sK3)
    | ~ spl11_2
    | ~ spl11_21
    | ~ spl11_42 ),
    inference(resolution,[],[f547,f557])).

fof(f568,plain,
    ( spl11_1
    | ~ spl11_2
    | spl11_43 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | spl11_43 ),
    inference(subsumption_resolution,[],[f566,f43])).

fof(f566,plain,
    ( v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | spl11_43 ),
    inference(subsumption_resolution,[],[f565,f46])).

fof(f565,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_1
    | ~ spl11_2
    | spl11_43 ),
    inference(subsumption_resolution,[],[f564,f87])).

fof(f564,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | spl11_43 ),
    inference(subsumption_resolution,[],[f563,f90])).

fof(f563,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_43 ),
    inference(resolution,[],[f561,f72])).

fof(f561,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl11_43 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl11_43
  <=> m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f562,plain,
    ( spl11_42
    | ~ spl11_43
    | ~ spl11_8
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f553,f324,f168,f559,f555])).

fof(f324,plain,
    ( spl11_22
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X1)
        | r1_lattice3(sK2,sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f553,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ spl11_8
    | ~ spl11_22 ),
    inference(resolution,[],[f170,f325])).

fof(f325,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK3,X1) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f324])).

fof(f534,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f532,f43])).

fof(f532,plain,
    ( v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f531,f46])).

fof(f531,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f530,f475])).

fof(f475,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl11_34
  <=> r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f530,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f529,f91])).

fof(f91,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f529,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f525,f86])).

fof(f86,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f525,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(resolution,[],[f521,f74])).

fof(f521,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f519,f91])).

fof(f519,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl11_1
    | ~ spl11_21
    | ~ spl11_34 ),
    inference(resolution,[],[f516,f475])).

fof(f516,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,X2))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK3,X2))
        | r2_yellow_0(sK2,X2) )
    | ~ spl11_1
    | ~ spl11_21 ),
    inference(resolution,[],[f514,f86])).

fof(f502,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_35 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | spl11_35 ),
    inference(subsumption_resolution,[],[f500,f43])).

fof(f500,plain,
    ( v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | spl11_35 ),
    inference(subsumption_resolution,[],[f499,f46])).

fof(f499,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | spl11_35 ),
    inference(subsumption_resolution,[],[f498,f91])).

fof(f498,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_35 ),
    inference(subsumption_resolution,[],[f497,f86])).

fof(f497,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK4)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_35 ),
    inference(resolution,[],[f479,f72])).

fof(f479,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl11_35 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl11_35
  <=> m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f480,plain,
    ( spl11_34
    | ~ spl11_35
    | ~ spl11_1
    | spl11_2
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f471,f324,f89,f85,f477,f473])).

fof(f471,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f417,f91])).

fof(f417,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl11_1
    | ~ spl11_22 ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl11_1
    | ~ spl11_22 ),
    inference(resolution,[],[f325,f180])).

fof(f180,plain,
    ( ! [X3] :
        ( r1_lattice3(sK2,X3,sK9(sK2,sK3,X3))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X3))
        | r2_yellow_0(sK2,X3) )
    | ~ spl11_1 ),
    inference(resolution,[],[f86,f103])).

fof(f470,plain,
    ( ~ spl11_10
    | ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f468,f177])).

fof(f177,plain,
    ( sP0(sK2,sK3)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f468,plain,
    ( ~ sP0(sK2,sK3)
    | ~ spl11_33 ),
    inference(resolution,[],[f458,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f458,plain,
    ( r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl11_33
  <=> r2_yellow_0(sK2,sK7(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f462,plain,
    ( ~ spl11_10
    | spl11_32 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl11_10
    | spl11_32 ),
    inference(subsumption_resolution,[],[f460,f177])).

fof(f460,plain,
    ( ~ sP0(sK2,sK3)
    | spl11_32 ),
    inference(resolution,[],[f453,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f453,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3))
    | spl11_32 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl11_32
  <=> m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f459,plain,
    ( spl11_33
    | ~ spl11_32
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f445,f175,f451,f456])).

fof(f445,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3))
    | r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ spl11_10 ),
    inference(resolution,[],[f177,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X1),k1_zfmisc_1(sK3))
      | r2_yellow_0(sK2,sK7(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK2,sK7(X0,X1))
      | ~ m1_subset_1(sK7(X0,X1),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ sQ10_eqProxy(k1_xboole_0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f63,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK7(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X6] :
      ( sQ10_eqProxy(k1_xboole_0,X6)
      | r2_yellow_0(sK2,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X6) ) ),
    inference(equality_proxy_replacement,[],[f49,f75])).

fof(f49,plain,(
    ! [X6] :
      ( r2_yellow_0(sK2,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f443,plain,
    ( spl11_10
    | spl11_21
    | ~ spl11_12
    | spl11_13
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f442,f313,f203,f199,f317,f175])).

fof(f313,plain,
    ( spl11_20
  <=> m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,X0)
        | sP0(sK2,sK3)
        | ~ r1_lattice3(sK2,sK3,X0) )
    | ~ spl11_12
    | spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f441,f47])).

fof(f441,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,X0)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK3,X0) )
    | ~ spl11_12
    | spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f440,f48])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,X0)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK3,X0) )
    | ~ spl11_12
    | spl11_13
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f439,f314])).

fof(f314,plain,
    ( m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f439,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK3,X0) )
    | ~ spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f362,f204])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP1(sK4,sK2,sK3)
        | r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK3,X0) )
    | ~ spl11_12 ),
    inference(resolution,[],[f201,f278])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f277,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X2,sK2,X0)
      | m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f157,f43])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f156,f44])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f155,f46])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f277,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f276,f52])).

fof(f52,plain,(
    ! [X4] :
      ( r2_yellow_0(sK2,sK5(X4))
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f275,f50])).

fof(f50,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | v1_finset_1(sK5(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ v1_finset_1(sK5(sK8(sK2,X0,X2)))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f274,f43])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ v1_finset_1(sK5(sK8(sK2,X0,X2)))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f273,f44])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ v1_finset_1(sK5(sK8(sK2,X0,X2)))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f272,f45])).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ v1_finset_1(sK5(sK8(sK2,X0,X2)))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f271,f46])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X0,X2)))
      | ~ m1_subset_1(sK5(sK8(sK2,X0,X2)),k1_zfmisc_1(X0))
      | ~ v1_finset_1(sK5(sK8(sK2,X0,X2)))
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X0,X2),sK4)
      | ~ m1_subset_1(sK8(sK2,X0,X2),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    ! [X4] :
      ( sQ10_eqProxy(k2_yellow_0(sK2,sK5(X4)),X4)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(equality_proxy_replacement,[],[f53,f75])).

fof(f53,plain,(
    ! [X4] :
      ( k2_yellow_0(sK2,sK5(X4)) = X4
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sQ10_eqProxy(k2_yellow_0(X0,X5),sK8(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r1_lattice3(X0,X2,X3)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f67,f75])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f201,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f361,plain,
    ( ~ spl11_23
    | ~ spl11_12
    | spl11_20 ),
    inference(avatar_split_clause,[],[f342,f313,f199,f328])).

fof(f328,plain,
    ( spl11_23
  <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f342,plain,
    ( ~ r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl11_20 ),
    inference(resolution,[],[f315,f51])).

fof(f51,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f315,plain,
    ( ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | spl11_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f359,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f357,f91])).

fof(f357,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f350,f250])).

fof(f250,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f249,f43])).

fof(f249,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f248,f46])).

fof(f248,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f247,f91])).

fof(f247,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_1
    | spl11_2
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f246,f86])).

fof(f246,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl11_2
    | ~ spl11_14 ),
    inference(resolution,[],[f244,f74])).

fof(f244,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | spl11_2
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f237,f91])).

fof(f237,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl11_14 ),
    inference(factoring,[],[f208])).

fof(f208,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl11_14
  <=> ! [X1] :
        ( r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f350,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | spl11_2
    | ~ spl11_14
    | ~ spl11_19 ),
    inference(resolution,[],[f302,f244])).

fof(f302,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1) )
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl11_19
  <=> ! [X1] :
        ( r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f345,plain,
    ( ~ spl11_12
    | spl11_23 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl11_12
    | spl11_23 ),
    inference(subsumption_resolution,[],[f343,f330])).

fof(f330,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl11_23 ),
    inference(avatar_component_clause,[],[f328])).

fof(f343,plain,
    ( m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl11_12 ),
    inference(resolution,[],[f308,f48])).

fof(f308,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X3))
        | m1_subset_1(sK8(sK2,sK3,sK4),X3) )
    | ~ spl11_12 ),
    inference(resolution,[],[f201,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f326,plain,
    ( spl11_10
    | ~ spl11_20
    | spl11_22
    | ~ spl11_12
    | spl11_13 ),
    inference(avatar_split_clause,[],[f322,f203,f199,f324,f313,f175])).

fof(f322,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ r1_lattice3(sK2,sK4,X1) )
    | ~ spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f321,f47])).

fof(f321,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK4,X1) )
    | ~ spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f320,f48])).

fof(f320,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK4,X1) )
    | ~ spl11_12
    | spl11_13 ),
    inference(subsumption_resolution,[],[f305,f204])).

fof(f305,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP1(sK4,sK2,sK3)
        | r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
        | sP0(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_lattice3(sK2,sK4,X1) )
    | ~ spl11_12 ),
    inference(resolution,[],[f201,f258])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f257,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X0,sK2,X2)
      | m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f228,f43])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f227,f44])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f226,f46])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f68,f45])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f256,f52])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f255,f50])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ v1_finset_1(sK5(sK8(sK2,X2,X0)))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f254,f43])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ v1_finset_1(sK5(sK8(sK2,X2,X0)))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f253,f44])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ v1_finset_1(sK5(sK8(sK2,X2,X0)))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f252,f45])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ v1_finset_1(sK5(sK8(sK2,X2,X0)))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f251,f46])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X0,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_yellow_0(sK2,sK5(sK8(sK2,X2,X0)))
      | ~ m1_subset_1(sK5(sK8(sK2,X2,X0)),k1_zfmisc_1(X2))
      | ~ v1_finset_1(sK5(sK8(sK2,X2,X0)))
      | sP0(sK2,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ r2_hidden(sK8(sK2,X2,X0),sK4)
      | ~ m1_subset_1(sK8(sK2,X2,X0),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f81,f77])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sQ10_eqProxy(k2_yellow_0(X0,X5),sK8(X0,X1,X2))
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r1_lattice3(X0,X1,X3)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f70,f75])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | k2_yellow_0(X0,X5) != sK8(X0,X1,X2)
      | ~ r2_yellow_0(X0,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X5)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f303,plain,
    ( spl11_12
    | spl11_19
    | spl11_13
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f299,f292,f203,f301,f199])).

fof(f292,plain,
    ( spl11_18
  <=> ! [X1,X0] :
        ( r2_hidden(sK8(sK2,sK3,X0),X0)
        | r2_yellow_0(sK2,X1)
        | ~ r1_lattice3(sK2,X0,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | sP1(X0,sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f299,plain,
    ( ! [X1] :
        ( r2_yellow_0(sK2,X1)
        | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4) )
    | spl11_13
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f296,f204])).

fof(f296,plain,
    ( ! [X1] :
        ( r2_yellow_0(sK2,X1)
        | ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | sP1(sK4,sK2,sK3)
        | r2_hidden(sK8(sK2,sK3,sK4),sK4) )
    | ~ spl11_18 ),
    inference(resolution,[],[f293,f48])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_yellow_0(sK2,X1)
        | ~ r1_lattice3(sK2,X0,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | sP1(X0,sK2,sK3)
        | r2_hidden(sK8(sK2,sK3,X0),X0) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl11_10
    | spl11_18
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f287,f85,f292,f175])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(sK2,sK3,X0),X0)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | ~ r1_lattice3(sK2,X0,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1) )
    | ~ spl11_1 ),
    inference(resolution,[],[f284,f47])).

fof(f284,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,X5,X4),X4)
        | sP0(sK2,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(X4,sK2,X5)
        | r1_lattice3(sK2,X5,sK9(sK2,sK3,X6))
        | ~ r1_lattice3(sK2,X4,sK9(sK2,sK3,X6))
        | r2_yellow_0(sK2,X6) )
    | ~ spl11_1 ),
    inference(resolution,[],[f123,f86])).

fof(f232,plain,
    ( ~ spl11_13
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl11_13
    | spl11_16 ),
    inference(subsumption_resolution,[],[f230,f205])).

fof(f230,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | spl11_16 ),
    inference(resolution,[],[f219,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f219,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3))
    | spl11_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl11_16
  <=> m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f220,plain,
    ( spl11_15
    | ~ spl11_16
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f210,f203,f217,f213])).

fof(f210,plain,
    ( ~ m1_subset_1(sK6(sK4,sK2,sK3),k1_zfmisc_1(sK3))
    | r2_hidden(k2_yellow_0(sK2,sK6(sK4,sK2,sK3)),sK4)
    | ~ spl11_13 ),
    inference(resolution,[],[f205,f101])).

fof(f101,plain,(
    ! [X4,X2,X3] :
      ( ~ sP1(X2,X3,X4)
      | ~ m1_subset_1(sK6(X2,X3,X4),k1_zfmisc_1(sK3))
      | r2_hidden(k2_yellow_0(sK2,sK6(X2,X3,X4)),sK4) ) ),
    inference(subsumption_resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k2_yellow_0(sK2,sK6(X2,X3,X4)),sK4)
      | ~ m1_subset_1(sK6(X2,X3,X4),k1_zfmisc_1(sK3))
      | ~ v1_finset_1(sK6(X2,X3,X4))
      | ~ sP1(X2,X3,X4) ) ),
    inference(resolution,[],[f76,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ10_eqProxy(k1_xboole_0,sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_proxy_replacement,[],[f59,f75])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK6(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X3] :
      ( sQ10_eqProxy(k1_xboole_0,X3)
      | r2_hidden(k2_yellow_0(sK2,X3),sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3) ) ),
    inference(equality_proxy_replacement,[],[f54,f75])).

fof(f54,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK2,X3),sK4)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f209,plain,
    ( spl11_12
    | spl11_13
    | spl11_14
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f195,f191,f207,f203,f199])).

fof(f191,plain,
    ( spl11_11
  <=> ! [X3,X2] :
        ( r2_hidden(sK8(sK2,sK3,X2),X2)
        | r1_lattice3(sK2,X3,sK9(sK2,sK3,X3))
        | r2_yellow_0(sK2,X3)
        | sP1(X2,sK2,sK3)
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f195,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1)
        | sP1(sK4,sK2,sK3)
        | r1_lattice3(sK2,sK4,sK9(sK2,sK3,X1))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4) )
    | ~ spl11_11 ),
    inference(resolution,[],[f192,f48])).

fof(f192,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X3,sK9(sK2,sK3,X3))
        | r2_yellow_0(sK2,X3)
        | sP1(X2,sK2,sK3)
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,X3))
        | r2_hidden(sK8(sK2,sK3,X2),X2) )
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl11_10
    | spl11_11
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f189,f85,f191,f175])).

fof(f189,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK8(sK2,sK3,X2),X2)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,X3))
        | sP1(X2,sK2,sK3)
        | r2_yellow_0(sK2,X3)
        | r1_lattice3(sK2,X3,sK9(sK2,sK3,X3)) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f187,f47])).

fof(f187,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK8(sK2,sK3,X2),X2)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,X3))
        | sP1(X2,sK2,sK3)
        | r2_yellow_0(sK2,X3)
        | r1_lattice3(sK2,X3,sK9(sK2,sK3,X3)) )
    | ~ spl11_1 ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK8(sK2,sK3,X2),X2)
        | sP0(sK2,sK3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X2,sK9(sK2,sK3,X3))
        | sP1(X2,sK2,sK3)
        | r2_yellow_0(sK2,X3)
        | r1_lattice3(sK2,X3,sK9(sK2,sK3,X3))
        | r2_yellow_0(sK2,X3) )
    | ~ spl11_1 ),
    inference(resolution,[],[f179,f180])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK2,X1,sK9(sK2,sK3,X2))
        | r2_hidden(sK8(sK2,X1,X0),X0)
        | sP0(sK2,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X0,sK9(sK2,sK3,X2))
        | sP1(X0,sK2,X1)
        | r2_yellow_0(sK2,X2) )
    | ~ spl11_1 ),
    inference(resolution,[],[f86,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | sP1(X3,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X3),X3)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | r2_yellow_0(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | sP1(X3,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X3),X3)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f114,f46])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(sK2,X0,sK9(sK2,X1,X2))
      | sP1(X3,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X3),X3)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X3,sK9(sK2,X1,X2))
      | ~ r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,X2)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f113,f72])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1) ) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | sP1(X2,sK2,X0)
      | r2_hidden(sK8(sK2,X0,X2),X2)
      | sP0(sK2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X2,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f66,f45])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f178,plain,
    ( spl11_8
    | spl11_9
    | spl11_10
    | spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f166,f89,f85,f175,f172,f168])).

fof(f166,plain,
    ( ! [X0] :
        ( sP0(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,sK3,X0),X0)
        | r1_lattice3(sK2,X0,sK9(sK2,sK4,sK3))
        | sP1(X0,sK2,sK3)
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3)) )
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f162,f87])).

fof(f162,plain,
    ( ! [X0] :
        ( sP0(sK2,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,sK3,X0),X0)
        | r1_lattice3(sK2,X0,sK9(sK2,sK4,sK3))
        | sP1(X0,sK2,sK3)
        | r2_yellow_0(sK2,sK3)
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3)) )
    | ~ spl11_2 ),
    inference(resolution,[],[f129,f47])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP0(sK2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(sK8(sK2,X0,X1),X1)
        | r1_lattice3(sK2,X1,sK9(sK2,sK4,X0))
        | sP1(X1,sK2,X0)
        | r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,X0)) )
    | ~ spl11_2 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK8(sK2,X0,X1),X1)
        | sP0(sK2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X1,sK9(sK2,sK4,X0))
        | sP1(X1,sK2,X0)
        | r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,X0))
        | r2_yellow_0(sK2,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f124,f104])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,X0,sK9(sK2,sK4,X0))
        | r1_lattice3(sK2,sK4,sK9(sK2,sK4,X0))
        | r2_yellow_0(sK2,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f103,f90])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK2,X1,sK9(sK2,sK4,X2))
        | r2_hidden(sK8(sK2,X1,X0),X0)
        | sP0(sK2,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | r1_lattice3(sK2,X0,sK9(sK2,sK4,X2))
        | sP1(X0,sK2,X1)
        | r2_yellow_0(sK2,X2) )
    | ~ spl11_2 ),
    inference(resolution,[],[f116,f90])).

fof(f93,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f55,f89,f85])).

fof(f55,plain,
    ( r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f56,f89,f85])).

fof(f56,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
