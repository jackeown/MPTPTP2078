%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1678+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  235 (1410 expanded)
%              Number of leaves         :   30 ( 501 expanded)
%              Depth                    :   23
%              Number of atoms          : 1603 (23652 expanded)
%              Number of equality atoms :  106 (3110 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f489,f718,f730,f741,f752,f760,f768,f807,f812,f817,f822,f969,f1054,f1107,f1410,f1549,f1564,f1674,f2071])).

fof(f2071,plain,
    ( ~ spl10_38
    | ~ spl10_40
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_43 ),
    inference(avatar_contradiction_clause,[],[f2070])).

fof(f2070,plain,
    ( $false
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_41
    | ~ spl10_42
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2069,f816])).

fof(f816,plain,
    ( r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f814])).

fof(f814,plain,
    ( spl10_42
  <=> r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f2069,plain,
    ( ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2068,f811])).

fof(f811,plain,
    ( m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl10_41
  <=> m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f2068,plain,
    ( ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f2067,f821])).

fof(f821,plain,
    ( v1_finset_1(sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl10_43
  <=> v1_finset_1(sK5(sK8(sK2,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f2067,plain,
    ( ~ v1_finset_1(sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(trivial_inequality_removal,[],[f2066])).

fof(f2066,plain,
    ( sK8(sK2,sK3,sK4) != sK8(sK2,sK3,sK4)
    | ~ v1_finset_1(sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(superposition,[],[f740,f806])).

fof(f806,plain,
    ( sK8(sK2,sK3,sK4) = k2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl10_40
  <=> sK8(sK2,sK3,sK4) = k2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f740,plain,
    ( ! [X3] :
        ( k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ r2_yellow_0(sK2,X3) )
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl10_38
  <=> ! [X3] :
        ( k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ r2_yellow_0(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f1674,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_61
    | ~ spl10_62 ),
    inference(avatar_contradiction_clause,[],[f1673])).

fof(f1673,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_61
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f1563,f1559])).

fof(f1559,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f1550,f77])).

fof(f77,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl10_2
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1550,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ spl10_1
    | ~ spl10_61 ),
    inference(resolution,[],[f1409,f1274])).

fof(f1274,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,X2))
        | ~ r1_lattice3(sK2,X2,sK9(sK2,sK3,X2))
        | r2_yellow_0(sK2,X2) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f1273,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f17,f21,f20,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_waybel_0)).

fof(f1273,plain,
    ( ! [X2] :
        ( r2_yellow_0(sK2,X2)
        | ~ r1_lattice3(sK2,X2,sK9(sK2,sK3,X2))
        | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,X2))
        | v2_struct_0(sK2) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f1266,f42])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f1266,plain,
    ( ! [X2] :
        ( r2_yellow_0(sK2,X2)
        | ~ r1_lattice3(sK2,X2,sK9(sK2,sK3,X2))
        | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK3,X2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_1 ),
    inference(resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f72,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_1
  <=> r2_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1409,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1407,plain,
    ( spl10_61
  <=> r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f1563,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f1561])).

fof(f1561,plain,
    ( spl10_62
  <=> r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f1564,plain,
    ( spl10_62
    | ~ spl10_60
    | ~ spl10_36
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f1551,f1407,f716,f1403,f1561])).

fof(f1403,plain,
    ( spl10_60
  <=> m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f716,plain,
    ( spl10_36
  <=> ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1551,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK9(sK2,sK3,sK4))
    | ~ spl10_36
    | ~ spl10_61 ),
    inference(resolution,[],[f1409,f717])).

fof(f717,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,X0) )
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f716])).

fof(f1549,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_60 ),
    inference(avatar_contradiction_clause,[],[f1548])).

fof(f1548,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | spl10_60 ),
    inference(subsumption_resolution,[],[f1547,f39])).

fof(f1547,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | spl10_60 ),
    inference(subsumption_resolution,[],[f1546,f42])).

fof(f1546,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2
    | spl10_60 ),
    inference(subsumption_resolution,[],[f1545,f72])).

fof(f1545,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_2
    | spl10_60 ),
    inference(subsumption_resolution,[],[f1537,f77])).

fof(f1537,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_60 ),
    inference(resolution,[],[f1405,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1405,plain,
    ( ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | spl10_60 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1410,plain,
    ( ~ spl10_60
    | spl10_61
    | ~ spl10_1
    | spl10_2
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f1401,f750,f75,f71,f1407,f1403])).

fof(f750,plain,
    ( spl10_39
  <=> ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f1401,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f1400,f77])).

fof(f1400,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_1
    | ~ spl10_39 ),
    inference(duplicate_literal_removal,[],[f1377])).

fof(f1377,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | r2_yellow_0(sK2,sK4)
    | ~ m1_subset_1(sK9(sK2,sK3,sK4),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK3,sK4))
    | ~ spl10_1
    | ~ spl10_39 ),
    inference(resolution,[],[f1272,f751])).

fof(f751,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK3,X4) )
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f750])).

fof(f1272,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | r2_yellow_0(sK2,X1) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f1271,f39])).

fof(f1271,plain,
    ( ! [X1] :
        ( r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | v2_struct_0(sK2) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f1265,f42])).

fof(f1265,plain,
    ( ! [X1] :
        ( r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,X1,sK9(sK2,sK3,X1))
        | r1_lattice3(sK2,sK3,sK9(sK2,sK3,X1))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_1 ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1107,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_36
    | spl10_44
    | ~ spl10_45 ),
    inference(avatar_contradiction_clause,[],[f1106])).

fof(f1106,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_36
    | spl10_44
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f1105,f963])).

fof(f963,plain,
    ( ~ r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl10_44 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl10_44
  <=> r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f1105,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_36
    | ~ spl10_45 ),
    inference(subsumption_resolution,[],[f1097,f557])).

fof(f557,plain,
    ( m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f215,f76])).

fof(f76,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK2,X0)
        | m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2)) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f214,f39])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK2,X0)
        | m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f211,f42])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK2,X0)
        | m1_subset_1(sK9(sK2,X0,sK3),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1 ),
    inference(resolution,[],[f73,f67])).

fof(f73,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1097,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ spl10_36
    | ~ spl10_45 ),
    inference(resolution,[],[f968,f717])).

fof(f968,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f966])).

fof(f966,plain,
    ( spl10_45
  <=> r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f1054,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_39
    | ~ spl10_44 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_39
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f984,f988])).

fof(f988,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f987,f39])).

fof(f987,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f986,f42])).

fof(f986,plain,
    ( ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f985,f76])).

fof(f985,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl10_1
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f977,f73])).

fof(f977,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_44 ),
    inference(resolution,[],[f964,f69])).

fof(f964,plain,
    ( r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f962])).

fof(f984,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_39
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f976,f557])).

fof(f976,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | ~ spl10_39
    | ~ spl10_44 ),
    inference(resolution,[],[f964,f751])).

fof(f969,plain,
    ( spl10_44
    | spl10_45
    | spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f955,f75,f71,f966,f962])).

fof(f955,plain,
    ( r1_lattice3(sK2,sK3,sK9(sK2,sK4,sK3))
    | r1_lattice3(sK2,sK4,sK9(sK2,sK4,sK3))
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f217,f76])).

fof(f217,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,sK3,sK9(sK2,X1,sK3))
        | r1_lattice3(sK2,X1,sK9(sK2,X1,sK3)) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f216,f39])).

fof(f216,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,sK3,sK9(sK2,X1,sK3))
        | r1_lattice3(sK2,X1,sK9(sK2,X1,sK3))
        | v2_struct_0(sK2) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f212,f42])).

fof(f212,plain,
    ( ! [X1] :
        ( ~ r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,sK3,sK9(sK2,X1,sK3))
        | r1_lattice3(sK2,X1,sK9(sK2,X1,sK3))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_1 ),
    inference(resolution,[],[f73,f68])).

fof(f822,plain,
    ( ~ spl10_35
    | spl10_43
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f802,f727,f819,f712])).

fof(f712,plain,
    ( spl10_35
  <=> m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f727,plain,
    ( spl10_37
  <=> r2_hidden(sK8(sK2,sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f802,plain,
    ( v1_finset_1(sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_37 ),
    inference(resolution,[],[f729,f46])).

fof(f46,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | v1_finset_1(sK5(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f729,plain,
    ( r2_hidden(sK8(sK2,sK3,sK4),sK4)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f727])).

fof(f817,plain,
    ( ~ spl10_35
    | spl10_42
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f801,f727,f814,f712])).

fof(f801,plain,
    ( r2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_37 ),
    inference(resolution,[],[f729,f48])).

fof(f48,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | r2_yellow_0(sK2,sK5(X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f812,plain,
    ( ~ spl10_35
    | spl10_41
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f800,f727,f809,f712])).

fof(f800,plain,
    ( m1_subset_1(sK5(sK8(sK2,sK3,sK4)),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_37 ),
    inference(resolution,[],[f729,f47])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | m1_subset_1(sK5(X4),k1_zfmisc_1(sK3))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f807,plain,
    ( ~ spl10_35
    | spl10_40
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f799,f727,f804,f712])).

fof(f799,plain,
    ( sK8(sK2,sK3,sK4) = k2_yellow_0(sK2,sK5(sK8(sK2,sK3,sK4)))
    | ~ m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ spl10_37 ),
    inference(resolution,[],[f729,f49])).

fof(f49,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK4)
      | k2_yellow_0(sK2,sK5(X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f768,plain,
    ( spl10_38
    | spl10_39
    | spl10_18 ),
    inference(avatar_split_clause,[],[f767,f270,f750,f739])).

fof(f270,plain,
    ( spl10_18
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f767,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f766,f39])).

fof(f766,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f765,f40])).

fof(f40,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f765,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f764,f41])).

fof(f41,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f764,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f763,f42])).

fof(f763,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f762,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f762,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f761,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f761,plain,
    ( ! [X6,X7] :
        ( r1_lattice3(sK2,sK3,X6)
        | ~ r1_lattice3(sK2,sK4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
        | ~ r2_yellow_0(sK2,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X7)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f703,f271])).

fof(f271,plain,
    ( ~ sP0(sK2,sK3)
    | spl10_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f703,plain,(
    ! [X6,X7] :
      ( r1_lattice3(sK2,sK3,X6)
      | ~ r1_lattice3(sK2,sK4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK2))
      | sK8(sK2,sK3,sK4) != k2_yellow_0(sK2,X7)
      | ~ r2_yellow_0(sK2,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X7)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(definition_folding,[],[f10,f14,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f697,plain,(
    ~ sP1(sK4,sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f692])).

fof(f692,plain,
    ( ~ sP1(sK4,sK2,sK3)
    | ~ sP1(sK4,sK2,sK3) ),
    inference(resolution,[],[f685,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_yellow_0(X1,sK6(X0,X1,X2)),X0)
        & k1_xboole_0 != sK6(X0,X1,X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
        & v1_finset_1(sK6(X0,X1,X2)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X1,X3),X0)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X2))
          & v1_finset_1(X3) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,X3),X2)
          & k1_xboole_0 != X3
          & m1_subset_1(X3,k1_zfmisc_1(X1))
          & v1_finset_1(X3) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f685,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK2,sK6(X0,X1,sK3)),sK4)
      | ~ sP1(X0,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f684,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK6(X0,X1,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f684,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK2,sK6(X0,X1,sK3)),sK4)
      | ~ v1_finset_1(sK6(X0,X1,sK3))
      | ~ sP1(X0,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f682,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != sK6(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f682,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK6(X0,X1,sK3)
      | r2_hidden(k2_yellow_0(sK2,sK6(X0,X1,sK3)),sK4)
      | ~ v1_finset_1(sK6(X0,X1,sK3))
      | ~ sP1(X0,X1,sK3) ) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | k1_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK2,X3),sK4)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f760,plain,
    ( spl10_37
    | spl10_39
    | spl10_18 ),
    inference(avatar_split_clause,[],[f759,f270,f750,f727])).

fof(f759,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f758,f39])).

fof(f758,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f757,f40])).

fof(f757,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f756,f41])).

fof(f756,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f755,f42])).

fof(f755,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f754,f43])).

fof(f754,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f753,f44])).

fof(f753,plain,
    ( ! [X5] :
        ( r1_lattice3(sK2,sK3,X5)
        | ~ r1_lattice3(sK2,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f702,f271])).

fof(f702,plain,(
    ! [X5] :
      ( r1_lattice3(sK2,sK3,X5)
      | ~ r1_lattice3(sK2,sK4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | r2_hidden(sK8(sK2,sK3,sK4),sK4)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f752,plain,
    ( spl10_35
    | spl10_39
    | spl10_18 ),
    inference(avatar_split_clause,[],[f748,f270,f750,f712])).

fof(f748,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2)) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f747,f39])).

fof(f747,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f746,f40])).

fof(f746,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f745,f41])).

fof(f745,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f744,f42])).

fof(f744,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f743,f43])).

fof(f743,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f742,f44])).

fof(f742,plain,
    ( ! [X4] :
        ( r1_lattice3(sK2,sK3,X4)
        | ~ r1_lattice3(sK2,sK4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f701,f271])).

fof(f701,plain,(
    ! [X4] :
      ( r1_lattice3(sK2,sK3,X4)
      | ~ r1_lattice3(sK2,sK4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f741,plain,
    ( spl10_38
    | spl10_36
    | spl10_18 ),
    inference(avatar_split_clause,[],[f737,f270,f716,f739])).

fof(f737,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f736,f39])).

fof(f736,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f735,f40])).

fof(f735,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f734,f41])).

fof(f734,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f733,f42])).

fof(f733,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f732,f43])).

fof(f732,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f731,f44])).

fof(f731,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK2,sK4,X2)
        | ~ r1_lattice3(sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
        | ~ r2_yellow_0(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f700,f271])).

fof(f700,plain,(
    ! [X2,X3] :
      ( r1_lattice3(sK2,sK4,X2)
      | ~ r1_lattice3(sK2,sK3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | k2_yellow_0(sK2,X3) != sK8(sK2,sK3,sK4)
      | ~ r2_yellow_0(sK2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK3))
      | ~ v1_finset_1(X3)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f63])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f730,plain,
    ( spl10_37
    | spl10_36
    | spl10_18 ),
    inference(avatar_split_clause,[],[f725,f270,f716,f727])).

fof(f725,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f724,f39])).

fof(f724,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f723,f40])).

fof(f723,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f722,f41])).

fof(f722,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f721,f42])).

fof(f721,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f720,f43])).

fof(f720,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f719,f44])).

fof(f719,plain,
    ( ! [X1] :
        ( r1_lattice3(sK2,sK4,X1)
        | ~ r1_lattice3(sK2,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(sK8(sK2,sK3,sK4),sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f699,f271])).

fof(f699,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,sK4,X1)
      | ~ r1_lattice3(sK2,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(sK8(sK2,sK3,sK4),sK4)
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f718,plain,
    ( spl10_35
    | spl10_36
    | spl10_18 ),
    inference(avatar_split_clause,[],[f710,f270,f716,f712])).

fof(f710,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2)) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f709,f39])).

fof(f709,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f708,f40])).

fof(f708,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f707,f41])).

fof(f707,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f706,f42])).

fof(f706,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f705,f43])).

fof(f705,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f704,f44])).

fof(f704,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,sK4,X0)
        | ~ r1_lattice3(sK2,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl10_18 ),
    inference(subsumption_resolution,[],[f698,f271])).

fof(f698,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,sK4,X0)
      | ~ r1_lattice3(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | m1_subset_1(sK8(sK2,sK3,sK4),u1_struct_0(sK2))
      | sP0(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f697,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP1(X2,X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f489,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f487,f443])).

fof(f443,plain,
    ( v1_finset_1(sK7(sK2,sK3))
    | ~ spl10_18 ),
    inference(resolution,[],[f272,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_finset_1(sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r2_yellow_0(X0,sK7(X0,X1))
        & k1_xboole_0 != sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK7(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,X2)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X6] :
          ( ~ r2_yellow_0(X0,X6)
          & k1_xboole_0 != X6
          & m1_subset_1(X6,k1_zfmisc_1(X1))
          & v1_finset_1(X6) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f272,plain,
    ( sP0(sK2,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f487,plain,
    ( ~ v1_finset_1(sK7(sK2,sK3))
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f486,f446])).

fof(f446,plain,
    ( ~ r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ spl10_18 ),
    inference(resolution,[],[f272,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,sK7(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f486,plain,
    ( r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ v1_finset_1(sK7(sK2,sK3))
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f483,f445])).

fof(f445,plain,
    ( k1_xboole_0 != sK7(sK2,sK3)
    | ~ spl10_18 ),
    inference(resolution,[],[f272,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK7(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f483,plain,
    ( k1_xboole_0 = sK7(sK2,sK3)
    | r2_yellow_0(sK2,sK7(sK2,sK3))
    | ~ v1_finset_1(sK7(sK2,sK3))
    | ~ spl10_18 ),
    inference(resolution,[],[f444,f45])).

fof(f45,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK3))
      | k1_xboole_0 = X6
      | r2_yellow_0(sK2,X6)
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f444,plain,
    ( m1_subset_1(sK7(sK2,sK3),k1_zfmisc_1(sK3))
    | ~ spl10_18 ),
    inference(resolution,[],[f272,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f51,f75,f71])).

fof(f51,plain,
    ( r2_yellow_0(sK2,sK4)
    | r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f52,f75,f71])).

fof(f52,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | ~ r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
