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
% DateTime   : Thu Dec  3 13:17:18 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.84s
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
    ( sQ7_eqProxy(sK6(sK0,sK2,sK3),k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
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
    ( sQ7_eqProxy(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1581,f1578,f91])).

fof(f91,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | sQ7_eqProxy(k2_yellow_0(sK0,sK4(X5)),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(equality_proxy_replacement,[],[f59,f89])).

fof(f59,plain,(
    ! [X5] :
      ( k2_yellow_0(sK0,sK4(X5)) = X5
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_lattice3(sK0,sK2,sK3)
      | ~ r1_lattice3(sK0,sK1,sK3) )
    & ( r1_lattice3(sK0,sK2,sK3)
      | r1_lattice3(sK0,sK1,sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & ! [X4] :
        ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
        | ~ v1_finset_1(X4) )
    & ! [X5] :
        ( ( k2_yellow_0(sK0,sK4(X5)) = X5
          & r2_yellow_0(sK0,sK4(X5))
          & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
          & v1_finset_1(sK4(X5)) )
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    & ! [X7] :
        ( r2_yellow_0(sK0,X7)
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
                    ( ( ~ r1_lattice3(X0,X2,X3)
                      | ~ r1_lattice3(X0,X1,X3) )
                    & ( r1_lattice3(X0,X2,X3)
                      | r1_lattice3(X0,X1,X3) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X4] :
                    ( r2_hidden(k2_yellow_0(X0,X4),X2)
                    | k1_xboole_0 = X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                    | ~ v1_finset_1(X4) )
                & ! [X5] :
                    ( ? [X6] :
                        ( k2_yellow_0(X0,X6) = X5
                        & r2_yellow_0(X0,X6)
                        & m1_subset_1(X6,k1_zfmisc_1(X1))
                        & v1_finset_1(X6) )
                    | ~ r2_hidden(X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & ! [X7] :
                    ( r2_yellow_0(X0,X7)
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
                  ( ( ~ r1_lattice3(sK0,X2,X3)
                    | ~ r1_lattice3(sK0,X1,X3) )
                  & ( r1_lattice3(sK0,X2,X3)
                    | r1_lattice3(sK0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & ! [X4] :
                  ( r2_hidden(k2_yellow_0(sK0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k2_yellow_0(sK0,X6) = X5
                      & r2_yellow_0(sK0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              & ! [X7] :
                  ( r2_yellow_0(sK0,X7)
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
                ( ( ~ r1_lattice3(sK0,X2,X3)
                  | ~ r1_lattice3(sK0,X1,X3) )
                & ( r1_lattice3(sK0,X2,X3)
                  | r1_lattice3(sK0,X1,X3) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & ! [X4] :
                ( r2_hidden(k2_yellow_0(sK0,X4),X2)
                | k1_xboole_0 = X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X4) )
            & ! [X5] :
                ( ? [X6] :
                    ( k2_yellow_0(sK0,X6) = X5
                    & r2_yellow_0(sK0,X6)
                    & m1_subset_1(X6,k1_zfmisc_1(X1))
                    & v1_finset_1(X6) )
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            & ! [X7] :
                ( r2_yellow_0(sK0,X7)
                | k1_xboole_0 = X7
                | ~ m1_subset_1(X7,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X7) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_lattice3(sK0,X2,X3)
                | ~ r1_lattice3(sK0,sK1,X3) )
              & ( r1_lattice3(sK0,X2,X3)
                | r1_lattice3(sK0,sK1,X3) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & ! [X4] :
              ( r2_hidden(k2_yellow_0(sK0,X4),X2)
              | k1_xboole_0 = X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
              | ~ v1_finset_1(X4) )
          & ! [X5] :
              ( ? [X6] :
                  ( k2_yellow_0(sK0,X6) = X5
                  & r2_yellow_0(sK0,X6)
                  & m1_subset_1(X6,k1_zfmisc_1(sK1))
                  & v1_finset_1(X6) )
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          & ! [X7] :
              ( r2_yellow_0(sK0,X7)
              | k1_xboole_0 = X7
              | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
              | ~ v1_finset_1(X7) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_lattice3(sK0,X2,X3)
              | ~ r1_lattice3(sK0,sK1,X3) )
            & ( r1_lattice3(sK0,X2,X3)
              | r1_lattice3(sK0,sK1,X3) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & ! [X4] :
            ( r2_hidden(k2_yellow_0(sK0,X4),X2)
            | k1_xboole_0 = X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X4) )
        & ! [X5] :
            ( ? [X6] :
                ( k2_yellow_0(sK0,X6) = X5
                & r2_yellow_0(sK0,X6)
                & m1_subset_1(X6,k1_zfmisc_1(sK1))
                & v1_finset_1(X6) )
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & ! [X7] :
            ( r2_yellow_0(sK0,X7)
            | k1_xboole_0 = X7
            | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X7) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ r1_lattice3(sK0,sK2,X3)
            | ~ r1_lattice3(sK0,sK1,X3) )
          & ( r1_lattice3(sK0,sK2,X3)
            | r1_lattice3(sK0,sK1,X3) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & ! [X4] :
          ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
          | k1_xboole_0 = X4
          | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X4) )
      & ! [X5] :
          ( ? [X6] :
              ( k2_yellow_0(sK0,X6) = X5
              & r2_yellow_0(sK0,X6)
              & m1_subset_1(X6,k1_zfmisc_1(sK1))
              & v1_finset_1(X6) )
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
      & ! [X7] :
          ( r2_yellow_0(sK0,X7)
          | k1_xboole_0 = X7
          | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X7) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( ~ r1_lattice3(sK0,sK2,X3)
          | ~ r1_lattice3(sK0,sK1,X3) )
        & ( r1_lattice3(sK0,sK2,X3)
          | r1_lattice3(sK0,sK1,X3) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ~ r1_lattice3(sK0,sK2,sK3)
        | ~ r1_lattice3(sK0,sK1,sK3) )
      & ( r1_lattice3(sK0,sK2,sK3)
        | r1_lattice3(sK0,sK1,sK3) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5] :
      ( ? [X6] :
          ( k2_yellow_0(sK0,X6) = X5
          & r2_yellow_0(sK0,X6)
          & m1_subset_1(X6,k1_zfmisc_1(sK1))
          & v1_finset_1(X6) )
     => ( k2_yellow_0(sK0,sK4(X5)) = X5
        & r2_yellow_0(sK0,sK4(X5))
        & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
        & v1_finset_1(sK4(X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | r1_lattice3(X0,X1,X3) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X4] :
                  ( r2_hidden(k2_yellow_0(X0,X4),X2)
                  | k1_xboole_0 = X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              & ! [X5] :
                  ( ? [X6] :
                      ( k2_yellow_0(X0,X6) = X5
                      & r2_yellow_0(X0,X6)
                      & m1_subset_1(X6,k1_zfmisc_1(X1))
                      & v1_finset_1(X6) )
                  | ~ r2_hidden(X5,X2)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & ! [X7] :
                  ( r2_yellow_0(X0,X7)
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
                  ( ( ~ r1_lattice3(X0,X2,X7)
                    | ~ r1_lattice3(X0,X1,X7) )
                  & ( r1_lattice3(X0,X2,X7)
                    | r1_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( ~ r1_lattice3(X0,X2,X7)
                    | ~ r1_lattice3(X0,X1,X7) )
                  & ( r1_lattice3(X0,X2,X7)
                    | r1_lattice3(X0,X1,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
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
    inference(rectify,[],[f13])).

% (28145)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
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

fof(f1578,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f127,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

% (28137)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f127,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_2
  <=> r1_lattice3(sK0,sK2,sK3) ),
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
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1988,plain,
    ( ~ sQ7_eqProxy(sK6(sK0,sK2,sK3),k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
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
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f1662,f1698,f1964,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f1964,plain,
    ( ~ r1_orders_2(sK0,sK3,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
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
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f61,f127,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1698,plain,
    ( r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f122,f61,f1694,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | r1_lattice3(X0,X1,X3) ) ),
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
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1662,plain,
    ( r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1581,f1578,f58])).

fof(f58,plain,(
    ! [X5] :
      ( r2_yellow_0(sK0,sK4(X5))
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
    inference(unit_resulting_resolution,[],[f52,f237,f1483,f1508,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
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
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f161,f891,f306,f237,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f76,f89])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f306,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f160,f117,f294,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f89])).

fof(f294,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f290,f82])).

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

fof(f290,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f280,f83])).

fof(f280,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f126,f61,f273,f71])).

fof(f273,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f61,f241,f237,f67])).

fof(f241,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f123,f61,f81])).

fof(f123,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f126,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f160,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f66,f134,f159,f90])).

fof(f90,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | sQ7_eqProxy(k1_xboole_0,X4)
      | r2_hidden(k2_yellow_0(sK0,X4),sK2)
      | ~ v1_finset_1(X4) ) ),
    inference(equality_proxy_replacement,[],[f60,f89])).

fof(f60,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
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

fof(f891,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f237,f237,f745,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f745,plain,
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
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f131,f123,f61,f71])).

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
    ( r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f66,f134,f159,f92])).

fof(f92,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | sQ7_eqProxy(k1_xboole_0,X7)
      | r2_yellow_0(sK0,X7)
      | ~ v1_finset_1(X7) ) ),
    inference(equality_proxy_replacement,[],[f55,f89])).

fof(f55,plain,(
    ! [X7] :
      ( r2_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1483,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f52,f237,f161,f891,f306,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f77,f89])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
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
    inference(unit_resulting_resolution,[],[f52,f161,f891,f306,f237,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f75,f89])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f125,f121])).

fof(f62,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f63,f125,f121])).

fof(f63,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (28138)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (28143)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (28140)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (28146)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (28144)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (28151)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (28152)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (28148)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (28136)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (28134)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (28147)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (28142)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (28139)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.54  % (28150)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.55  % (28141)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.55  % (28135)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.61/0.57  % (28149)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.61/0.58  % (28146)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.84/0.59  % SZS output start Proof for theBenchmark
% 1.84/0.59  fof(f1994,plain,(
% 1.84/0.59    $false),
% 1.84/0.59    inference(avatar_sat_refutation,[],[f128,f129,f1573,f1993])).
% 1.84/0.59  fof(f1993,plain,(
% 1.84/0.59    ~spl8_1 | spl8_2),
% 1.84/0.59    inference(avatar_contradiction_clause,[],[f1992])).
% 1.84/0.59  fof(f1992,plain,(
% 1.84/0.59    $false | (~spl8_1 | spl8_2)),
% 1.84/0.59    inference(subsumption_resolution,[],[f1988,f1966])).
% 1.84/0.59  fof(f1966,plain,(
% 1.84/0.59    sQ7_eqProxy(sK6(sK0,sK2,sK3),k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1660,f118])).
% 1.84/0.59  fof(f118,plain,(
% 1.84/0.59    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | sQ7_eqProxy(X1,X0)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f89,plain,(
% 1.84/0.59    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 1.84/0.59    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 1.84/0.59  fof(f1660,plain,(
% 1.84/0.59    sQ7_eqProxy(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3)) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1581,f1578,f91])).
% 1.84/0.59  fof(f91,plain,(
% 1.84/0.59    ( ! [X5] : (~r2_hidden(X5,sK2) | sQ7_eqProxy(k2_yellow_0(sK0,sK4(X5)),X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.84/0.59    inference(equality_proxy_replacement,[],[f59,f89])).
% 1.84/0.59  fof(f59,plain,(
% 1.84/0.59    ( ! [X5] : (k2_yellow_0(sK0,sK4(X5)) = X5 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f39,plain,(
% 1.84/0.59    ((((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.84/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).
% 1.84/0.59  fof(f34,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f35,plain,(
% 1.84/0.59    ? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f36,plain,(
% 1.84/0.59    ? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f37,plain,(
% 1.84/0.59    ? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f38,plain,(
% 1.84/0.59    ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f33,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.84/0.59    inference(rectify,[],[f32])).
% 1.84/0.59  fof(f32,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.84/0.59    inference(flattening,[],[f31])).
% 1.84/0.59  fof(f31,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.84/0.59    inference(nnf_transformation,[],[f18])).
% 1.84/0.59  fof(f18,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.84/0.59    inference(flattening,[],[f17])).
% 1.84/0.59  fof(f17,plain,(
% 1.84/0.59    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.84/0.59    inference(ennf_transformation,[],[f16])).
% 1.84/0.59  fof(f16,plain,(
% 1.84/0.59    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.84/0.59    inference(pure_predicate_removal,[],[f14])).
% 1.84/0.59  fof(f14,plain,(
% 1.84/0.59    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.84/0.59    inference(rectify,[],[f13])).
% 1.84/0.59  % (28145)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.84/0.59  fof(f13,negated_conjecture,(
% 1.84/0.59    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.84/0.59    inference(negated_conjecture,[],[f12])).
% 1.84/0.59  fof(f12,conjecture,(
% 1.84/0.59    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).
% 1.84/0.59  fof(f1578,plain,(
% 1.84/0.59    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f61,f127,f79])).
% 1.84/0.59  fof(f79,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f48])).
% 1.84/0.59  fof(f48,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 1.84/0.59  fof(f47,plain,(
% 1.84/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f46,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(rectify,[],[f45])).
% 1.84/0.59  fof(f45,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(nnf_transformation,[],[f24])).
% 1.84/0.59  fof(f24,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(flattening,[],[f23])).
% 1.84/0.59  % (28137)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.84/0.59  fof(f23,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(ennf_transformation,[],[f8])).
% 1.84/0.59  fof(f8,axiom,(
% 1.84/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 1.84/0.59  fof(f127,plain,(
% 1.84/0.59    ~r1_lattice3(sK0,sK2,sK3) | spl8_2),
% 1.84/0.59    inference(avatar_component_clause,[],[f125])).
% 1.84/0.59  fof(f125,plain,(
% 1.84/0.59    spl8_2 <=> r1_lattice3(sK0,sK2,sK3)),
% 1.84/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.84/0.59  fof(f61,plain,(
% 1.84/0.59    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f52,plain,(
% 1.84/0.59    l1_orders_2(sK0)),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f1581,plain,(
% 1.84/0.59    r2_hidden(sK6(sK0,sK2,sK3),sK2) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f61,f127,f80])).
% 1.84/0.59  fof(f80,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f48])).
% 1.84/0.59  fof(f1988,plain,(
% 1.84/0.59    ~sQ7_eqProxy(sK6(sK0,sK2,sK3),k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | (~spl8_1 | spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1578,f117,f1983,f105])).
% 1.84/0.59  fof(f105,plain,(
% 1.84/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | m1_subset_1(X1,X3)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f1983,plain,(
% 1.84/0.59    ~m1_subset_1(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0)) | (~spl8_1 | spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f61,f1662,f1698,f1964,f87])).
% 1.84/0.59  fof(f87,plain,(
% 1.84/0.59    ( ! [X4,X0,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(equality_resolution,[],[f74])).
% 1.84/0.59  fof(f74,plain,(
% 1.84/0.59    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f44])).
% 1.84/0.59  fof(f44,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.84/0.59  fof(f43,plain,(
% 1.84/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.84/0.59    introduced(choice_axiom,[])).
% 1.84/0.59  fof(f42,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(rectify,[],[f41])).
% 1.84/0.59  fof(f41,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(flattening,[],[f40])).
% 1.84/0.59  fof(f40,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(nnf_transformation,[],[f22])).
% 1.84/0.59  fof(f22,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(flattening,[],[f21])).
% 1.84/0.59  fof(f21,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(ennf_transformation,[],[f9])).
% 1.84/0.59  fof(f9,axiom,(
% 1.84/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 1.84/0.59  fof(f1964,plain,(
% 1.84/0.59    ~r1_orders_2(sK0,sK3,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f117,f117,f1577,f1660,f112])).
% 1.84/0.59  fof(f112,plain,(
% 1.84/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_orders_2(X0,X2,X4) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X4,X5) | ~sQ7_eqProxy(X0,X1) | r1_orders_2(X1,X3,X5)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f1577,plain,(
% 1.84/0.59    ~r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f61,f127,f81])).
% 1.84/0.59  fof(f81,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f48])).
% 1.84/0.59  fof(f1698,plain,(
% 1.84/0.59    r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl8_1 | spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f122,f61,f1694,f71])).
% 1.84/0.59  fof(f71,plain,(
% 1.84/0.59    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r1_lattice3(X0,X1,X3)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f20])).
% 1.84/0.59  fof(f20,plain,(
% 1.84/0.59    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(ennf_transformation,[],[f11])).
% 1.84/0.59  fof(f11,axiom,(
% 1.84/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 1.84/0.59  fof(f1694,plain,(
% 1.84/0.59    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1661,f83])).
% 1.84/0.59  fof(f83,plain,(
% 1.84/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f26])).
% 1.84/0.59  fof(f26,plain,(
% 1.84/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.84/0.59    inference(ennf_transformation,[],[f15])).
% 1.84/0.59  fof(f15,plain,(
% 1.84/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.84/0.59    inference(unused_predicate_definition_removal,[],[f4])).
% 1.84/0.59  fof(f4,axiom,(
% 1.84/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.84/0.59  fof(f1661,plain,(
% 1.84/0.59    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1581,f1578,f57])).
% 1.84/0.59  fof(f57,plain,(
% 1.84/0.59    ( ! [X5] : (~r2_hidden(X5,sK2) | m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f122,plain,(
% 1.84/0.59    r1_lattice3(sK0,sK1,sK3) | ~spl8_1),
% 1.84/0.59    inference(avatar_component_clause,[],[f121])).
% 1.84/0.59  fof(f121,plain,(
% 1.84/0.59    spl8_1 <=> r1_lattice3(sK0,sK1,sK3)),
% 1.84/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.84/0.59  fof(f1662,plain,(
% 1.84/0.59    r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl8_2),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f1581,f1578,f58])).
% 1.84/0.59  fof(f58,plain,(
% 1.84/0.59    ( ! [X5] : (r2_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f117,plain,(
% 1.84/0.59    ( ! [X0] : (sQ7_eqProxy(X0,X0)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f1573,plain,(
% 1.84/0.59    spl8_1 | ~spl8_2),
% 1.84/0.59    inference(avatar_contradiction_clause,[],[f1572])).
% 1.84/0.59  fof(f1572,plain,(
% 1.84/0.59    $false | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(subsumption_resolution,[],[f1552,f1511])).
% 1.84/0.59  fof(f1511,plain,(
% 1.84/0.59    ~m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f237,f1483,f1508,f67])).
% 1.84/0.59  fof(f67,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f19])).
% 1.84/0.59  fof(f19,plain,(
% 1.84/0.59    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.84/0.59    inference(ennf_transformation,[],[f10])).
% 1.84/0.59  fof(f10,axiom,(
% 1.84/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.84/0.59  fof(f1508,plain,(
% 1.84/0.59    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f161,f891,f306,f237,f94])).
% 1.84/0.59  fof(f94,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r1_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)) )),
% 1.84/0.59    inference(equality_proxy_replacement,[],[f76,f89])).
% 1.84/0.59  fof(f76,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | r1_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f44])).
% 1.84/0.59  fof(f306,plain,(
% 1.84/0.59    ~sQ7_eqProxy(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3)) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f160,f117,f294,f104])).
% 1.84/0.59  fof(f104,plain,(
% 1.84/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f294,plain,(
% 1.84/0.59    ~r2_hidden(sK6(sK0,sK1,sK3),sK2) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f290,f82])).
% 1.84/0.59  fof(f82,plain,(
% 1.84/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f25])).
% 1.84/0.59  fof(f25,plain,(
% 1.84/0.59    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.84/0.59    inference(ennf_transformation,[],[f3])).
% 1.84/0.59  fof(f3,axiom,(
% 1.84/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.84/0.59  fof(f290,plain,(
% 1.84/0.59    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK2)) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f280,f83])).
% 1.84/0.59  fof(f280,plain,(
% 1.84/0.59    ~r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2) | (spl8_1 | ~spl8_2)),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f126,f61,f273,f71])).
% 1.84/0.59  fof(f273,plain,(
% 1.84/0.59    ~r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f61,f241,f237,f67])).
% 1.84/0.59  fof(f241,plain,(
% 1.84/0.59    ~r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3)) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f123,f61,f81])).
% 1.84/0.59  fof(f123,plain,(
% 1.84/0.59    ~r1_lattice3(sK0,sK1,sK3) | spl8_1),
% 1.84/0.59    inference(avatar_component_clause,[],[f121])).
% 1.84/0.59  fof(f126,plain,(
% 1.84/0.59    r1_lattice3(sK0,sK2,sK3) | ~spl8_2),
% 1.84/0.59    inference(avatar_component_clause,[],[f125])).
% 1.84/0.59  fof(f160,plain,(
% 1.84/0.59    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f66,f134,f159,f90])).
% 1.84/0.59  fof(f90,plain,(
% 1.84/0.59    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK1)) | sQ7_eqProxy(k1_xboole_0,X4) | r2_hidden(k2_yellow_0(sK0,X4),sK2) | ~v1_finset_1(X4)) )),
% 1.84/0.59    inference(equality_proxy_replacement,[],[f60,f89])).
% 1.84/0.59  fof(f60,plain,(
% 1.84/0.59    ( ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f39])).
% 1.84/0.59  fof(f159,plain,(
% 1.84/0.59    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f157,f82])).
% 1.84/0.59  fof(f157,plain,(
% 1.84/0.59    r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f123,f61,f80])).
% 1.84/0.59  fof(f134,plain,(
% 1.84/0.59    ( ! [X0] : (~sQ7_eqProxy(k1_xboole_0,k1_tarski(X0))) )),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f65,f64,f103])).
% 1.84/0.59  fof(f103,plain,(
% 1.84/0.59    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ7_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 1.84/0.59    inference(equality_proxy_axiom,[],[f89])).
% 1.84/0.59  fof(f64,plain,(
% 1.84/0.59    v1_xboole_0(k1_xboole_0)),
% 1.84/0.59    inference(cnf_transformation,[],[f1])).
% 1.84/0.59  fof(f1,axiom,(
% 1.84/0.59    v1_xboole_0(k1_xboole_0)),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.84/0.59  fof(f65,plain,(
% 1.84/0.59    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f2])).
% 1.84/0.59  fof(f2,axiom,(
% 1.84/0.59    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.84/0.59  fof(f66,plain,(
% 1.84/0.59    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f5])).
% 1.84/0.59  fof(f5,axiom,(
% 1.84/0.59    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 1.84/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 1.84/0.59  fof(f891,plain,(
% 1.84/0.59    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f52,f237,f237,f745,f68])).
% 1.84/0.59  fof(f68,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.59    inference(cnf_transformation,[],[f19])).
% 1.84/0.59  fof(f745,plain,(
% 1.84/0.59    r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 1.84/0.59    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f266,f237,f85])).
% 1.84/0.60  fof(f85,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f49])).
% 1.84/0.60  fof(f49,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.84/0.60    inference(nnf_transformation,[],[f30])).
% 1.84/0.60  fof(f30,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.84/0.60    inference(flattening,[],[f29])).
% 1.84/0.60  fof(f29,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f6])).
% 1.84/0.60  fof(f6,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.84/0.60  fof(f266,plain,(
% 1.84/0.60    r3_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f50,f51,f52,f237,f238,f84])).
% 1.84/0.60  fof(f84,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f28])).
% 1.84/0.60  fof(f28,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.84/0.60    inference(flattening,[],[f27])).
% 1.84/0.60  fof(f27,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f7])).
% 1.84/0.60  fof(f7,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 1.84/0.60  fof(f238,plain,(
% 1.84/0.60    m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK3),u1_struct_0(sK0)) | spl8_1),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f52,f171,f61,f79])).
% 1.84/0.60  fof(f171,plain,(
% 1.84/0.60    ~r1_lattice3(sK0,u1_struct_0(sK0),sK3) | spl8_1),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f52,f131,f123,f61,f71])).
% 1.84/0.60  fof(f131,plain,(
% 1.84/0.60    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f53,f83])).
% 1.84/0.60  fof(f53,plain,(
% 1.84/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f51,plain,(
% 1.84/0.60    v3_orders_2(sK0)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f50,plain,(
% 1.84/0.60    ~v2_struct_0(sK0)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f161,plain,(
% 1.84/0.60    r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl8_1),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f66,f134,f159,f92])).
% 1.84/0.60  fof(f92,plain,(
% 1.84/0.60    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(sK1)) | sQ7_eqProxy(k1_xboole_0,X7) | r2_yellow_0(sK0,X7) | ~v1_finset_1(X7)) )),
% 1.84/0.60    inference(equality_proxy_replacement,[],[f55,f89])).
% 1.84/0.60  fof(f55,plain,(
% 1.84/0.60    ( ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f1483,plain,(
% 1.84/0.60    ~r1_orders_2(sK0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | (spl8_1 | ~spl8_2)),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f52,f237,f161,f891,f306,f93])).
% 1.84/0.60  fof(f93,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X2) | sQ7_eqProxy(k2_yellow_0(X0,X1),X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.60    inference(equality_proxy_replacement,[],[f77,f89])).
% 1.84/0.60  fof(f77,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f44])).
% 1.84/0.60  fof(f237,plain,(
% 1.84/0.60    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | spl8_1),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f52,f123,f61,f79])).
% 1.84/0.60  fof(f1552,plain,(
% 1.84/0.60    m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 1.84/0.60    inference(unit_resulting_resolution,[],[f52,f161,f891,f306,f237,f95])).
% 1.84/0.60  fof(f95,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)) )),
% 1.84/0.60    inference(equality_proxy_replacement,[],[f75,f89])).
% 1.84/0.60  fof(f75,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X1) = X2 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f44])).
% 1.84/0.60  fof(f129,plain,(
% 1.84/0.60    spl8_1 | spl8_2),
% 1.84/0.60    inference(avatar_split_clause,[],[f62,f125,f121])).
% 1.84/0.60  fof(f62,plain,(
% 1.84/0.60    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f128,plain,(
% 1.84/0.60    ~spl8_1 | ~spl8_2),
% 1.84/0.60    inference(avatar_split_clause,[],[f63,f125,f121])).
% 1.84/0.60  fof(f63,plain,(
% 1.84/0.60    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  % SZS output end Proof for theBenchmark
% 1.84/0.60  % (28146)------------------------------
% 1.84/0.60  % (28146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (28146)Termination reason: Refutation
% 1.84/0.60  
% 1.84/0.60  % (28146)Memory used [KB]: 11513
% 1.84/0.60  % (28146)Time elapsed: 0.159 s
% 1.84/0.60  % (28146)------------------------------
% 1.84/0.60  % (28146)------------------------------
% 1.84/0.60  % (28131)Success in time 0.24 s
%------------------------------------------------------------------------------
