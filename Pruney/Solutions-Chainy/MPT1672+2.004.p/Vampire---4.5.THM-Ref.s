%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:16 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  139 (3225 expanded)
%              Number of leaves         :   22 (1134 expanded)
%              Depth                    :   21
%              Number of atoms          :  873 (61225 expanded)
%              Number of equality atoms :   69 (7585 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f130,f1658,f2114])).

fof(f2114,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f2113])).

fof(f2113,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f2109,f2081])).

fof(f2081,plain,
    ( sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1749,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ sQ7_eqProxy(X0,X1)
      | sQ7_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f90,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f1749,plain,
    ( sQ7_eqProxy(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1666,f1663,f92])).

fof(f92,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | sQ7_eqProxy(k1_yellow_0(sK0,sK4(X5)),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(equality_proxy_replacement,[],[f58,f90])).

fof(f58,plain,(
    ! [X5] :
      ( k1_yellow_0(sK0,sK4(X5)) = X5
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f30,f35,f34,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f1663,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f60,f128,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f128,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_2
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f1666,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f60,f128,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2109,plain,
    ( ~ sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1663,f118,f2099,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X2)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X0,X1)
      | m1_subset_1(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f2099,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f60,f1751,f1793,f2079,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f2079,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK3)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f118,f118,f1662,f1749,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X4)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X4,X5)
      | ~ sQ7_eqProxy(X0,X1)
      | r1_orders_2(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f1662,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f60,f128,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1793,plain,
    ( r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f123,f60,f1789,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f1789,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1750,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1750,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1666,f1663,f56])).

fof(f56,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f123,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_1
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1751,plain,
    ( r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f1666,f1663,f57])).

fof(f57,plain,(
    ! [X5] :
      ( r1_yellow_0(sK0,sK4(X5))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f1658,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1657])).

fof(f1657,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1637,f1596])).

fof(f1596,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f250,f1568,f1593,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f1593,plain,
    ( r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f167,f938,f311,f250,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f75,f90])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f311,plain,
    ( ~ sQ7_eqProxy(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f166,f118,f306,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f306,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f299,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f299,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f127,f60,f292,f71])).

fof(f292,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f60,f254,f250,f68])).

fof(f254,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f124,f60,f80])).

fof(f124,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f127,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f166,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f137,f165,f91])).

fof(f91,plain,(
    ! [X4] :
      ( ~ v1_finset_1(X4)
      | sQ7_eqProxy(k1_xboole_0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | r2_hidden(k1_yellow_0(sK0,X4),sK2) ) ),
    inference(equality_proxy_replacement,[],[f59,f90])).

fof(f59,plain,(
    ! [X4] :
      ( r2_hidden(k1_yellow_0(sK0,X4),sK2)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f165,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f162,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f162,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f160,f82])).

fof(f160,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f124,f60,f79])).

fof(f137,plain,(
    ! [X0] : ~ sQ7_eqProxy(k1_xboole_0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f64,f63,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ7_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f90])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f65,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f938,plain,
    ( r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f250,f250,f794,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f794,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f49,f50,f51,f250,f279,f250,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f279,plain,
    ( r3_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f49,f50,f51,f250,f251,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f251,plain,
    ( m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK3),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f178,f60,f78])).

fof(f178,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK3)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f132,f124,f60,f71])).

fof(f132,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f52,f83])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f167,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f65,f137,f165,f93])).

fof(f93,plain,(
    ! [X7] :
      ( ~ v1_finset_1(X7)
      | sQ7_eqProxy(k1_xboole_0,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | r1_yellow_0(sK0,X7) ) ),
    inference(equality_proxy_replacement,[],[f54,f90])).

fof(f54,plain,(
    ! [X7] :
      ( r1_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1568,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f250,f167,f938,f311,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f76,f90])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f250,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f51,f124,f60,f78])).

fof(f1637,plain,
    ( m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f167,f938,f311,f250,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f74,f90])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f61,f126,f122])).

fof(f61,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f62,f126,f122])).

fof(f62,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:07:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (16232)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (16238)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (16251)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (16247)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (16240)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (16233)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (16239)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (16245)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (16241)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (16246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (16236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (16242)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (16235)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (16244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (16249)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (16237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (16243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (16248)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % (16231)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (16234)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (16250)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.90/0.59  % (16245)Refutation found. Thanks to Tanya!
% 1.90/0.59  % SZS status Theorem for theBenchmark
% 1.90/0.60  % SZS output start Proof for theBenchmark
% 1.90/0.60  fof(f2115,plain,(
% 1.90/0.60    $false),
% 1.90/0.60    inference(avatar_sat_refutation,[],[f129,f130,f1658,f2114])).
% 1.90/0.60  fof(f2114,plain,(
% 1.90/0.60    ~spl8_1 | spl8_2),
% 1.90/0.60    inference(avatar_contradiction_clause,[],[f2113])).
% 1.90/0.60  fof(f2113,plain,(
% 1.90/0.60    $false | (~spl8_1 | spl8_2)),
% 1.90/0.60    inference(subsumption_resolution,[],[f2109,f2081])).
% 1.90/0.60  fof(f2081,plain,(
% 1.90/0.60    sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1749,f119])).
% 1.90/0.60  fof(f119,plain,(
% 1.90/0.60    ( ! [X0,X1] : (~sQ7_eqProxy(X0,X1) | sQ7_eqProxy(X1,X0)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f90,plain,(
% 1.90/0.60    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 1.90/0.60    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 1.90/0.60  fof(f1749,plain,(
% 1.90/0.60    sQ7_eqProxy(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK6(sK0,sK2,sK3)) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1666,f1663,f92])).
% 1.90/0.60  fof(f92,plain,(
% 1.90/0.60    ( ! [X5] : (~r2_hidden(X5,sK2) | sQ7_eqProxy(k1_yellow_0(sK0,sK4(X5)),X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.90/0.60    inference(equality_proxy_replacement,[],[f58,f90])).
% 1.90/0.60  fof(f58,plain,(
% 1.90/0.60    ( ! [X5] : (k1_yellow_0(sK0,sK4(X5)) = X5 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f36,plain,(
% 1.90/0.60    ((((~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)) & (r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k1_yellow_0(sK0,sK4(X5)) = X5 & r1_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.90/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f30,f35,f34,f33,f32,f31])).
% 1.90/0.60  fof(f31,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,X1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f32,plain,(
% 1.90/0.60    ? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,X1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f33,plain,(
% 1.90/0.60    ? [X2] : (? [X3] : ((~r2_lattice3(sK0,X2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,X2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r2_lattice3(sK0,sK2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,sK2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f34,plain,(
% 1.90/0.60    ? [X3] : ((~r2_lattice3(sK0,sK2,X3) | ~r2_lattice3(sK0,sK1,X3)) & (r2_lattice3(sK0,sK2,X3) | r2_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)) & (r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f35,plain,(
% 1.90/0.60    ! [X5] : (? [X6] : (k1_yellow_0(sK0,X6) = X5 & r1_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k1_yellow_0(sK0,sK4(X5)) = X5 & r1_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f30,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) & (r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k1_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k1_yellow_0(X0,X6) = X5 & r1_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r1_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/0.60    inference(rectify,[],[f29])).
% 1.90/0.60  fof(f29,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/0.60    inference(flattening,[],[f28])).
% 1.90/0.60  fof(f28,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r2_lattice3(X0,X2,X7) | ~r2_lattice3(X0,X1,X7)) & (r2_lattice3(X0,X2,X7) | r2_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/0.60    inference(nnf_transformation,[],[f17])).
% 1.90/0.60  fof(f17,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.90/0.60    inference(flattening,[],[f16])).
% 1.90/0.60  fof(f16,plain,(
% 1.90/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.90/0.60    inference(ennf_transformation,[],[f15])).
% 1.90/0.60  fof(f15,plain,(
% 1.90/0.60    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 1.90/0.60    inference(pure_predicate_removal,[],[f14])).
% 1.90/0.60  fof(f14,plain,(
% 1.90/0.60    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 1.90/0.60    inference(rectify,[],[f13])).
% 1.90/0.60  fof(f13,negated_conjecture,(
% 1.90/0.60    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 1.90/0.60    inference(negated_conjecture,[],[f12])).
% 1.90/0.60  fof(f12,conjecture,(
% 1.90/0.60    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).
% 1.90/0.60  fof(f1663,plain,(
% 1.90/0.60    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f60,f128,f78])).
% 1.90/0.60  fof(f78,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f45])).
% 1.90/0.60  fof(f45,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK6(X0,X1,X2),X2) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.90/0.60  fof(f44,plain,(
% 1.90/0.60    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK6(X0,X1,X2),X2) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f43,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(rectify,[],[f42])).
% 1.90/0.60  fof(f42,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(nnf_transformation,[],[f23])).
% 1.90/0.60  fof(f23,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(flattening,[],[f22])).
% 1.90/0.60  fof(f22,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(ennf_transformation,[],[f8])).
% 1.90/0.60  fof(f8,axiom,(
% 1.90/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.90/0.60  fof(f128,plain,(
% 1.90/0.60    ~r2_lattice3(sK0,sK2,sK3) | spl8_2),
% 1.90/0.60    inference(avatar_component_clause,[],[f126])).
% 1.90/0.60  fof(f126,plain,(
% 1.90/0.60    spl8_2 <=> r2_lattice3(sK0,sK2,sK3)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.90/0.60  fof(f60,plain,(
% 1.90/0.60    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f51,plain,(
% 1.90/0.60    l1_orders_2(sK0)),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f1666,plain,(
% 1.90/0.60    r2_hidden(sK6(sK0,sK2,sK3),sK2) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f60,f128,f79])).
% 1.90/0.60  fof(f79,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f45])).
% 1.90/0.60  fof(f2109,plain,(
% 1.90/0.60    ~sQ7_eqProxy(sK6(sK0,sK2,sK3),k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | (~spl8_1 | spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1663,f118,f2099,f107])).
% 1.90/0.60  fof(f107,plain,(
% 1.90/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | m1_subset_1(X1,X3)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f2099,plain,(
% 1.90/0.60    ~m1_subset_1(k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0)) | (~spl8_1 | spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f60,f1751,f1793,f2079,f88])).
% 1.90/0.60  fof(f88,plain,(
% 1.90/0.60    ( ! [X4,X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(equality_resolution,[],[f73])).
% 1.90/0.60  fof(f73,plain,(
% 1.90/0.60    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f41])).
% 1.90/0.60  fof(f41,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 1.90/0.60  fof(f40,plain,(
% 1.90/0.60    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f39,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(rectify,[],[f38])).
% 1.90/0.60  fof(f38,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(flattening,[],[f37])).
% 1.90/0.60  fof(f37,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(nnf_transformation,[],[f21])).
% 1.90/0.60  fof(f21,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(flattening,[],[f20])).
% 1.90/0.60  fof(f20,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(ennf_transformation,[],[f9])).
% 1.90/0.60  fof(f9,axiom,(
% 1.90/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.90/0.60  fof(f2079,plain,(
% 1.90/0.60    ~r1_orders_2(sK0,k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),sK3) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f118,f118,f1662,f1749,f113])).
% 1.90/0.60  fof(f113,plain,(
% 1.90/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_orders_2(X0,X2,X4) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X4,X5) | ~sQ7_eqProxy(X0,X1) | r1_orders_2(X1,X3,X5)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f1662,plain,(
% 1.90/0.60    ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f60,f128,f80])).
% 1.90/0.60  fof(f80,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK6(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f45])).
% 1.90/0.60  fof(f1793,plain,(
% 1.90/0.60    r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl8_1 | spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f123,f60,f1789,f71])).
% 1.90/0.60  fof(f71,plain,(
% 1.90/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r2_lattice3(X0,X1,X3)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f19])).
% 1.90/0.60  fof(f19,plain,(
% 1.90/0.60    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(ennf_transformation,[],[f11])).
% 1.90/0.60  fof(f11,axiom,(
% 1.90/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 1.90/0.60  fof(f1789,plain,(
% 1.90/0.60    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1750,f83])).
% 1.90/0.60  fof(f83,plain,(
% 1.90/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f47])).
% 1.90/0.60  fof(f47,plain,(
% 1.90/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.90/0.60    inference(nnf_transformation,[],[f4])).
% 1.90/0.60  fof(f4,axiom,(
% 1.90/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.90/0.60  fof(f1750,plain,(
% 1.90/0.60    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1666,f1663,f56])).
% 1.90/0.60  fof(f56,plain,(
% 1.90/0.60    ( ! [X5] : (~r2_hidden(X5,sK2) | m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f123,plain,(
% 1.90/0.60    r2_lattice3(sK0,sK1,sK3) | ~spl8_1),
% 1.90/0.60    inference(avatar_component_clause,[],[f122])).
% 1.90/0.60  fof(f122,plain,(
% 1.90/0.60    spl8_1 <=> r2_lattice3(sK0,sK1,sK3)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.90/0.60  fof(f1751,plain,(
% 1.90/0.60    r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl8_2),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f1666,f1663,f57])).
% 1.90/0.60  fof(f57,plain,(
% 1.90/0.60    ( ! [X5] : (r1_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f118,plain,(
% 1.90/0.60    ( ! [X0] : (sQ7_eqProxy(X0,X0)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f1658,plain,(
% 1.90/0.60    spl8_1 | ~spl8_2),
% 1.90/0.60    inference(avatar_contradiction_clause,[],[f1657])).
% 1.90/0.60  fof(f1657,plain,(
% 1.90/0.60    $false | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(subsumption_resolution,[],[f1637,f1596])).
% 1.90/0.60  fof(f1596,plain,(
% 1.90/0.60    ~m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f250,f1568,f1593,f68])).
% 1.90/0.60  fof(f68,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X2,X1)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f18])).
% 1.90/0.60  fof(f18,plain,(
% 1.90/0.60    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.90/0.60    inference(ennf_transformation,[],[f10])).
% 1.90/0.60  fof(f10,axiom,(
% 1.90/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.90/0.60  fof(f1593,plain,(
% 1.90/0.60    r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))) | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f167,f938,f311,f250,f95])).
% 1.90/0.60  fof(f95,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)) )),
% 1.90/0.60    inference(equality_proxy_replacement,[],[f75,f90])).
% 1.90/0.60  fof(f75,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f41])).
% 1.90/0.60  fof(f311,plain,(
% 1.90/0.60    ~sQ7_eqProxy(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK6(sK0,sK1,sK3)) | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f166,f118,f306,f106])).
% 1.90/0.60  fof(f106,plain,(
% 1.90/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ7_eqProxy(X2,X3) | ~sQ7_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f306,plain,(
% 1.90/0.60    ~r2_hidden(sK6(sK0,sK1,sK3),sK2) | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f299,f82])).
% 1.90/0.60  fof(f82,plain,(
% 1.90/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f46])).
% 1.90/0.60  fof(f46,plain,(
% 1.90/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.90/0.60    inference(nnf_transformation,[],[f3])).
% 1.90/0.60  fof(f3,axiom,(
% 1.90/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.90/0.60  fof(f299,plain,(
% 1.90/0.60    ~r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK2) | (spl8_1 | ~spl8_2)),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f127,f60,f292,f71])).
% 1.90/0.60  fof(f292,plain,(
% 1.90/0.60    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f60,f254,f250,f68])).
% 1.90/0.60  fof(f254,plain,(
% 1.90/0.60    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f124,f60,f80])).
% 1.90/0.60  fof(f124,plain,(
% 1.90/0.60    ~r2_lattice3(sK0,sK1,sK3) | spl8_1),
% 1.90/0.60    inference(avatar_component_clause,[],[f122])).
% 1.90/0.60  fof(f127,plain,(
% 1.90/0.60    r2_lattice3(sK0,sK2,sK3) | ~spl8_2),
% 1.90/0.60    inference(avatar_component_clause,[],[f126])).
% 1.90/0.60  fof(f166,plain,(
% 1.90/0.60    r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f65,f137,f165,f91])).
% 1.90/0.60  fof(f91,plain,(
% 1.90/0.60    ( ! [X4] : (~v1_finset_1(X4) | sQ7_eqProxy(k1_xboole_0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | r2_hidden(k1_yellow_0(sK0,X4),sK2)) )),
% 1.90/0.60    inference(equality_proxy_replacement,[],[f59,f90])).
% 1.90/0.60  fof(f59,plain,(
% 1.90/0.60    ( ! [X4] : (r2_hidden(k1_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f36])).
% 1.90/0.60  fof(f165,plain,(
% 1.90/0.60    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f162,f84])).
% 1.90/0.60  fof(f84,plain,(
% 1.90/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f47])).
% 1.90/0.60  fof(f162,plain,(
% 1.90/0.60    r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f160,f82])).
% 1.90/0.60  fof(f160,plain,(
% 1.90/0.60    r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f124,f60,f79])).
% 1.90/0.60  fof(f137,plain,(
% 1.90/0.60    ( ! [X0] : (~sQ7_eqProxy(k1_xboole_0,k1_tarski(X0))) )),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f64,f63,f104])).
% 1.90/0.60  fof(f104,plain,(
% 1.90/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ7_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 1.90/0.60    inference(equality_proxy_axiom,[],[f90])).
% 1.90/0.60  fof(f63,plain,(
% 1.90/0.60    v1_xboole_0(k1_xboole_0)),
% 1.90/0.60    inference(cnf_transformation,[],[f1])).
% 1.90/0.60  fof(f1,axiom,(
% 1.90/0.60    v1_xboole_0(k1_xboole_0)),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.90/0.60  fof(f64,plain,(
% 1.90/0.60    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f2])).
% 1.90/0.60  fof(f2,axiom,(
% 1.90/0.60    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.90/0.60  fof(f65,plain,(
% 1.90/0.60    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f5])).
% 1.90/0.60  fof(f5,axiom,(
% 1.90/0.60    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 1.90/0.60  fof(f938,plain,(
% 1.90/0.60    r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f51,f250,f250,f794,f69])).
% 1.90/0.60  fof(f69,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,X1) | r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f18])).
% 1.90/0.60  fof(f794,plain,(
% 1.90/0.60    r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 1.90/0.60    inference(unit_resulting_resolution,[],[f49,f50,f51,f250,f279,f250,f86])).
% 1.90/0.60  fof(f86,plain,(
% 1.90/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f48])).
% 1.90/0.60  fof(f48,plain,(
% 1.90/0.60    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.90/0.60    inference(nnf_transformation,[],[f27])).
% 1.90/0.60  fof(f27,plain,(
% 1.90/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.90/0.60    inference(flattening,[],[f26])).
% 2.02/0.60  fof(f26,plain,(
% 2.02/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/0.60    inference(ennf_transformation,[],[f6])).
% 2.02/0.60  fof(f6,axiom,(
% 2.02/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.02/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 2.02/0.60  fof(f279,plain,(
% 2.02/0.60    r3_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl8_1),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f49,f50,f51,f250,f251,f85])).
% 2.02/0.60  fof(f85,plain,(
% 2.02/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.02/0.60    inference(cnf_transformation,[],[f25])).
% 2.02/0.60  fof(f25,plain,(
% 2.02/0.60    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.02/0.60    inference(flattening,[],[f24])).
% 2.02/0.60  fof(f24,plain,(
% 2.02/0.60    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.02/0.60    inference(ennf_transformation,[],[f7])).
% 2.02/0.60  fof(f7,axiom,(
% 2.02/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 2.02/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 2.02/0.60  fof(f251,plain,(
% 2.02/0.60    m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK3),u1_struct_0(sK0)) | spl8_1),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f51,f178,f60,f78])).
% 2.02/0.60  fof(f178,plain,(
% 2.02/0.60    ~r2_lattice3(sK0,u1_struct_0(sK0),sK3) | spl8_1),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f51,f132,f124,f60,f71])).
% 2.02/0.60  fof(f132,plain,(
% 2.02/0.60    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f52,f83])).
% 2.02/0.60  fof(f52,plain,(
% 2.02/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  fof(f50,plain,(
% 2.02/0.60    v3_orders_2(sK0)),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  fof(f49,plain,(
% 2.02/0.60    ~v2_struct_0(sK0)),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  fof(f167,plain,(
% 2.02/0.60    r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl8_1),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f65,f137,f165,f93])).
% 2.02/0.60  fof(f93,plain,(
% 2.02/0.60    ( ! [X7] : (~v1_finset_1(X7) | sQ7_eqProxy(k1_xboole_0,X7) | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | r1_yellow_0(sK0,X7)) )),
% 2.02/0.60    inference(equality_proxy_replacement,[],[f54,f90])).
% 2.02/0.60  fof(f54,plain,(
% 2.02/0.60    ( ! [X7] : (r1_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  fof(f1568,plain,(
% 2.02/0.60    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))) | (spl8_1 | ~spl8_2)),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f51,f250,f167,f938,f311,f94])).
% 2.02/0.60  fof(f94,plain,(
% 2.02/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.02/0.60    inference(equality_proxy_replacement,[],[f76,f90])).
% 2.02/0.60  fof(f76,plain,(
% 2.02/0.60    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.02/0.60    inference(cnf_transformation,[],[f41])).
% 2.02/0.60  fof(f250,plain,(
% 2.02/0.60    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | spl8_1),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f51,f124,f60,f78])).
% 2.02/0.60  fof(f1637,plain,(
% 2.02/0.60    m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2)),
% 2.02/0.60    inference(unit_resulting_resolution,[],[f51,f167,f938,f311,f250,f96])).
% 2.02/0.60  fof(f96,plain,(
% 2.02/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ7_eqProxy(k1_yellow_0(X0,X1),X2)) )),
% 2.02/0.60    inference(equality_proxy_replacement,[],[f74,f90])).
% 2.02/0.60  fof(f74,plain,(
% 2.02/0.60    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.02/0.60    inference(cnf_transformation,[],[f41])).
% 2.02/0.60  fof(f130,plain,(
% 2.02/0.60    spl8_1 | spl8_2),
% 2.02/0.60    inference(avatar_split_clause,[],[f61,f126,f122])).
% 2.02/0.60  fof(f61,plain,(
% 2.02/0.60    r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  fof(f129,plain,(
% 2.02/0.60    ~spl8_1 | ~spl8_2),
% 2.02/0.60    inference(avatar_split_clause,[],[f62,f126,f122])).
% 2.02/0.60  fof(f62,plain,(
% 2.02/0.60    ~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)),
% 2.02/0.60    inference(cnf_transformation,[],[f36])).
% 2.02/0.60  % SZS output end Proof for theBenchmark
% 2.02/0.60  % (16245)------------------------------
% 2.02/0.60  % (16245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.60  % (16245)Termination reason: Refutation
% 2.02/0.60  
% 2.02/0.60  % (16245)Memory used [KB]: 11513
% 2.02/0.60  % (16245)Time elapsed: 0.144 s
% 2.02/0.60  % (16245)------------------------------
% 2.02/0.60  % (16245)------------------------------
% 2.02/0.61  % (16230)Success in time 0.261 s
%------------------------------------------------------------------------------
