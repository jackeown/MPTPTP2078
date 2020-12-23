%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 (3220 expanded)
%              Number of leaves         :   22 (1131 expanded)
%              Depth                    :   21
%              Number of atoms          :  870 (61180 expanded)
%              Number of equality atoms :   69 (7585 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1994,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f129,f1573,f1993])).

fof(f1993,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1992])).

fof(f1992,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1988,f1966])).

fof(f1966,plain,
    ( sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1660,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | sQ7_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f89,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f1660,plain,
    ( sQ7_eqProxy(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1581,f1578,f91])).

fof(f91,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | sQ7_eqProxy(k1_yellow_0(sK0,sK4(X5)),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(equality_proxy_replacement,[],[f59,f89])).

fof(f59,plain,(
    ! [X5] :
      ( k1_yellow_0(sK0,sK4(X5)) = X5
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r2_lattice3(sK0,sK2,sK3)
      | ~ r2_lattice3(sK0,sK1,sK3) )
    & ( r2_lattice3(sK0,sK2,sK3)
      | r2_lattice3(sK0,sK1,sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & ! [X4] :
        ( r2_hidden(k1_yellow_0(sK0,X4),sK2)
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
        | ~ v1_finset_1(X4) )
    & ! [X5] :
        ( ( k1_yellow_0(sK0,sK4(X5)) = X5
          & r1_yellow_0(sK0,sK4(X5))
          & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
          & v1_finset_1(sK4(X5)) )
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    & ! [X7] :
        ( r1_yellow_0(sK0,X7)
        | k1_xboole_0 = X7
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
        | ~ v1_finset_1(X7) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_lattice3(X0,X1,X3) )
                    & ( r2_lattice3(X0,X2,X3)
                      | r2_lattice3(X0,X1,X3) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X4] :
                    ( r2_hidden(k1_yellow_0(X0,X4),X2)
                    | k1_xboole_0 = X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X4) )
                & ! [X5] :
                    ( ? [X6] :
                        ( k1_yellow_0(X0,X6) = X5
                        & r1_yellow_0(X0,X6)
                        & m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & ! [X7] :
                    ( r1_yellow_0(X0,X7)
                    | k1_xboole_0 = X7
                    | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X7) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK0,X2,X3)
                    | ~ r2_lattice3(sK0,X1,X3) )
                  & ( r2_lattice3(sK0,X2,X3)
                    | r2_lattice3(sK0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(sK0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(sK0,X6) = X5
                      & r1_yellow_0(sK0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              & ! [X7] :
                  ( r1_yellow_0(sK0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(sK0,X2,X3)
                  | ~ r2_lattice3(sK0,X1,X3) )
                & ( r2_lattice3(sK0,X2,X3)
                  | r2_lattice3(sK0,X1,X3) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & ! [X4] :
                ( r2_hidden(k1_yellow_0(sK0,X4),X2)
                | k1_xboole_0 = X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X4) )
            & ! [X5] :
                ( ? [X6] :
                    ( k1_yellow_0(sK0,X6) = X5
                    & r1_yellow_0(sK0,X6)
                    & m1_subset_1(X6,k1_zfmisc_1(X1))
                    & v1_finset_1(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            & ! [X7] :
                ( r1_yellow_0(sK0,X7)
                | k1_xboole_0 = X7
                | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X7) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(sK0,X2,X3)
                | ~ r2_lattice3(sK0,sK1,X3) )
              & ( r2_lattice3(sK0,X2,X3)
                | r2_lattice3(sK0,sK1,X3) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & ! [X4] :
              ( r2_hidden(k1_yellow_0(sK0,X4),X2)
              | k1_xboole_0 = X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
              | ~ v1_finset_1(X4) )
          & ! [X5] :
              ( ? [X6] :
                  ( k1_yellow_0(sK0,X6) = X5
                  & r1_yellow_0(sK0,X6)
                  & m1_subset_1(X6,k1_zfmisc_1(sK1))
                  & v1_finset_1(X6) )
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          & ! [X7] :
              ( r1_yellow_0(sK0,X7)
              | k1_xboole_0 = X7
              | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
              | ~ v1_finset_1(X7) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r2_lattice3(sK0,X2,X3)
              | ~ r2_lattice3(sK0,sK1,X3) )
            & ( r2_lattice3(sK0,X2,X3)
              | r2_lattice3(sK0,sK1,X3) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & ! [X4] :
            ( r2_hidden(k1_yellow_0(sK0,X4),X2)
            | k1_xboole_0 = X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X4) )
        & ! [X5] :
            ( ? [X6] :
                ( k1_yellow_0(sK0,X6) = X5
                & r1_yellow_0(sK0,X6)
                & m1_subset_1(X6,k1_zfmisc_1(sK1))
                & v1_finset_1(X6) )
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & ! [X7] :
            ( r1_yellow_0(sK0,X7)
            | k1_xboole_0 = X7
            | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X7) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ r2_lattice3(sK0,sK2,X3)
            | ~ r2_lattice3(sK0,sK1,X3) )
          & ( r2_lattice3(sK0,sK2,X3)
            | r2_lattice3(sK0,sK1,X3) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & ! [X4] :
          ( r2_hidden(k1_yellow_0(sK0,X4),sK2)
          | k1_xboole_0 = X4
          | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X4) )
      & ! [X5] :
          ( ? [X6] :
              ( k1_yellow_0(sK0,X6) = X5
              & r1_yellow_0(sK0,X6)
              & m1_subset_1(X6,k1_zfmisc_1(sK1))
              & v1_finset_1(X6) )
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
      & ! [X7] :
          ( r1_yellow_0(sK0,X7)
          | k1_xboole_0 = X7
          | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X7) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( ~ r2_lattice3(sK0,sK2,X3)
          | ~ r2_lattice3(sK0,sK1,X3) )
        & ( r2_lattice3(sK0,sK2,X3)
          | r2_lattice3(sK0,sK1,X3) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ~ r2_lattice3(sK0,sK2,sK3)
        | ~ r2_lattice3(sK0,sK1,sK3) )
      & ( r2_lattice3(sK0,sK2,sK3)
        | r2_lattice3(sK0,sK1,sK3) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5] :
      ( ? [X6] :
          ( k1_yellow_0(sK0,X6) = X5
          & r1_yellow_0(sK0,X6)
          & m1_subset_1(X6,k1_zfmisc_1(sK1))
          & v1_finset_1(X6) )
     => ( k1_yellow_0(sK0,sK4(X5)) = X5
        & r1_yellow_0(sK0,sK4(X5))
        & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
        & v1_finset_1(sK4(X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | r2_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k1_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k1_yellow_0(X0,X6) = X5
                      & r1_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r1_yellow_0(X0,X7)
                  | k1_xboole_0 = X7
                  | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X7) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r2_lattice3(X0,X2,X7)
                    | ~ r2_lattice3(X0,X1,X7) )
                  & ( r2_lattice3(X0,X2,X7)
                    | r2_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
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
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
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
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f1578,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f127,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f127,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_2
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1581,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f127,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1988,plain,
    ( ~ sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1578,f117,f1983,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X2)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X0,X1)
      | m1_subset_1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f1983,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f1662,f1698,f1964,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f1964,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK3)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f117,f117,f1577,f1660,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X4)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X4,X5)
      | ~ sQ7_eqProxy(X0,X1)
      | r1_orders_2(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f1577,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f127,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1698,plain,
    ( r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f122,f61,f1694,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f1694,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1661,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1661,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1581,f1578,f57])).

fof(f57,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_1
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1662,plain,
    ( r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1581,f1578,f58])).

fof(f58,plain,(
    ! [X5] :
      ( r1_yellow_0(sK0,sK4(X5))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f117,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f1573,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1552,f1511])).

fof(f1511,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f237,f1483,f1508,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f1508,plain,
    ( r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f161,f890,f312,f237,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f76,f89])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f312,plain,
    ( ~ sQ7_eqProxy(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f160,f117,f300,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f300,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f296,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f296,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f286,f83])).

fof(f286,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f126,f61,f279,f72])).

fof(f279,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f61,f241,f237,f69])).

fof(f241,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f123,f61,f81])).

fof(f123,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f126,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f160,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f66,f134,f159,f90])).

fof(f90,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | sQ7_eqProxy(k1_xboole_0,X4)
      | r2_hidden(k1_yellow_0(sK0,X4),sK2)
      | ~ v1_finset_1(X4) ) ),
    inference(equality_proxy_replacement,[],[f60,f89])).

fof(f60,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK0,X4),sK2)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f159,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f157,f82])).

fof(f157,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f123,f61,f80])).

fof(f134,plain,(
    ! [X0] : ~ sQ7_eqProxy(k1_xboole_0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f65,f64,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ7_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f66,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f890,plain,
    ( r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f237,f237,f752,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f752,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f266,f237,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f266,plain,
    ( r3_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f238,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f238,plain,
    ( m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK3),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f171,f61,f79])).

fof(f171,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f131,f123,f61,f72])).

fof(f131,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f83])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f161,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f66,f134,f159,f92])).

fof(f92,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | sQ7_eqProxy(k1_xboole_0,X7)
      | r1_yellow_0(sK0,X7)
      | ~ v1_finset_1(X7) ) ),
    inference(equality_proxy_replacement,[],[f55,f89])).

fof(f55,plain,(
    ! [X7] :
      ( r1_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1483,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f237,f161,f890,f312,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f77,f89])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f237,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f123,f61,f79])).

fof(f1552,plain,
    ( m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f161,f890,f312,f237,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f75,f89])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f125,f121])).

fof(f62,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f63,f125,f121])).

fof(f63,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (21059)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (21054)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (21055)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (21051)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (21048)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21065)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (21060)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (21046)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21057)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21045)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (21050)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (21063)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (21062)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (21049)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (21058)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (21047)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (21053)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (21064)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (21052)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (21056)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (21061)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (21059)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1994,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f128,f129,f1573,f1993])).
% 0.22/0.54  fof(f1993,plain,(
% 0.22/0.54    ~spl8_1 | spl8_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1992])).
% 0.22/0.54  fof(f1992,plain,(
% 0.22/0.54    $false | (~spl8_1 | spl8_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1988,f1966])).
% 0.22/0.54  fof(f1966,plain,(
% 0.22/0.54    sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1660,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | sQ7_eqProxy(X1,X0)) )),
% 0.22/0.54    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.22/0.54  fof(f1660,plain,(
% 0.22/0.54    sQ7_eqProxy(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3)) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1581,f1578,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X5] : (~r2_hidden(X5,sK2) | sQ7_eqProxy(k1_yellow_0(sK0,sK4(X5)),X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f59,f89])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X5] : (k1_yellow_0(sK0,sK4(X5)) = X5 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ((((~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)) & (r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK0,sK4(X5)) = X5 & r1_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,X1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,X1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r2_lattice3(sK0,sK2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,sK2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ? [X3] : ((~r2_lattice3(sK0,sK2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,sK2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)) & (r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k1_yellow_0(sK0,sK4(X5)) = X5 & r1_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 0.22/0.54    inference(rectify,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).
% 0.22/0.54  fof(f1578,plain,(
% 0.22/0.54    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f61,f127,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK6(X0,X1,X2),X2) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK6(X0,X1,X2),X2) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~r2_lattice3(sK0,sK2,sK3) | spl8_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f125])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    spl8_2 <=> r2_lattice3(sK0,sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    l1_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f1581,plain,(
% 0.22/0.54    r2_hidden(sK6(sK0,sK2,sK3),sK2) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f61,f127,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f1988,plain,(
% 0.22/0.54    ~sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | (~spl8_1 | spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1578,f117,f1983,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | m1_subset_1(X1,X3)) )),
% 0.22/0.54    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.54  fof(f1983,plain,(
% 0.22/0.54    ~m1_subset_1(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0)) | (~spl8_1 | spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f61,f1662,f1698,f1964,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.22/0.54  fof(f1964,plain,(
% 0.22/0.54    ~r1_orders_2(sK0,k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK3) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f117,f117,f1577,f1660,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_orders_2(X0,X2,X4) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X4,X5) | ~sQ7_eqProxy(X0,X1) | r1_orders_2(X1,X3,X5)) )),
% 0.22/0.54    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.54  fof(f1577,plain,(
% 0.22/0.54    ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f61,f127,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK6(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f1698,plain,(
% 0.22/0.54    r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl8_1 | spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f122,f61,f1694,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r2_lattice3(X0,X1,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.22/0.54  fof(f1694,plain,(
% 0.22/0.54    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1661,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f1661,plain,(
% 0.22/0.54    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1581,f1578,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X5] : (~r2_hidden(X5,sK2) | m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    r2_lattice3(sK0,sK1,sK3) | ~spl8_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl8_1 <=> r2_lattice3(sK0,sK1,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.54  fof(f1662,plain,(
% 0.22/0.54    r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl8_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f1581,f1578,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X5] : (r1_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0] : (sQ7_eqProxy(X0,X0)) )),
% 0.22/0.54    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.54  fof(f1573,plain,(
% 0.22/0.54    spl8_1 | ~spl8_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1572])).
% 0.22/0.54  fof(f1572,plain,(
% 0.22/0.54    $false | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1552,f1511])).
% 0.22/0.54  fof(f1511,plain,(
% 0.22/0.54    ~m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f237,f1483,f1508,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 0.22/0.54  fof(f1508,plain,(
% 0.22/0.54    r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f161,f890,f312,f237,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f76,f89])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    ~sQ7_eqProxy(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3)) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f160,f117,f300,f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 0.22/0.54    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~r2_hidden(sK6(sK0,sK1,sK3),sK2) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f296,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK2)) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f286,f83])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ~r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2) | (spl8_1 | ~spl8_2)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f126,f61,f279,f72])).
% 0.22/0.54  fof(f279,plain,(
% 0.22/0.54    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | spl8_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f61,f241,f237,f69])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3) | spl8_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f52,f123,f61,f81])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~r2_lattice3(sK0,sK1,sK3) | spl8_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    r2_lattice3(sK0,sK2,sK3) | ~spl8_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f125])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl8_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f66,f134,f159,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK1)) | sQ7_eqProxy(k1_xboole_0,X4) | r2_hidden(k1_yellow_0(sK0,X4),sK2) | ~v1_finset_1(X4)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f60,f89])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl8_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f157,f82])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f123,f61,f80])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ( ! [X0] : (~sQ7_eqProxy(k1_xboole_0,k1_tarski(X0))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f65,f64,f103])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ7_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.22/0.55    inference(equality_proxy_axiom,[],[f89])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 0.22/0.55  fof(f890,plain,(
% 0.22/0.55    r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f237,f237,f752,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,X1) | r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f752,plain,(
% 0.22/0.55    r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f266,f237,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.55  fof(f266,plain,(
% 0.22/0.55    r3_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f238,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.22/0.55  fof(f238,plain,(
% 0.22/0.55    m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK3),u1_struct_0(sK0)) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f171,f61,f79])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    ~r2_lattice3(sK0,u1_struct_0(sK0),sK3) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f131,f123,f61,f72])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f53,f83])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    v3_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f66,f134,f159,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(sK1)) | sQ7_eqProxy(k1_xboole_0,X7) | r1_yellow_0(sK0,X7) | ~v1_finset_1(X7)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f55,f89])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f1483,plain,(
% 0.22/0.55    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))) | (spl8_1 | ~spl8_2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f237,f161,f890,f312,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f77,f89])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | spl8_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f123,f61,f79])).
% 0.22/0.55  fof(f1552,plain,(
% 0.22/0.55    m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f52,f161,f890,f312,f237,f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)) )),
% 0.22/0.55    inference(equality_proxy_replacement,[],[f75,f89])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl8_1 | spl8_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f62,f125,f121])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ~spl8_1 | ~spl8_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f63,f125,f121])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (21059)------------------------------
% 0.22/0.55  % (21059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21059)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (21059)Memory used [KB]: 11513
% 0.22/0.55  % (21059)Time elapsed: 0.120 s
% 0.22/0.55  % (21059)------------------------------
% 0.22/0.55  % (21059)------------------------------
% 0.22/0.55  % (21044)Success in time 0.185 s
%------------------------------------------------------------------------------
