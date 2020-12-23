%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 577 expanded)
%              Number of leaves         :   46 ( 239 expanded)
%              Depth                    :   16
%              Number of atoms          : 1152 (6636 expanded)
%              Number of equality atoms :   80 ( 736 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f97,f101,f105,f113,f117,f121,f165,f170,f182,f240,f273,f275,f281,f335,f342,f441,f458,f828,f838,f847,f864,f869,f870,f914,f1034,f1061,f1081,f1222])).

fof(f1222,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | spl7_12
    | ~ spl7_4
    | ~ spl7_114 ),
    inference(avatar_split_clause,[],[f1220,f909,f103,f151,f271,f268])).

fof(f268,plain,
    ( spl7_30
  <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f271,plain,
    ( spl7_31
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f151,plain,
    ( spl7_12
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f103,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f909,plain,
    ( spl7_114
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f1220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_114 ),
    inference(resolution,[],[f910,f59])).

fof(f59,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f39,f38,f37,f36,f35])).

fof(f35,plain,
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
        & v4_orders_2(X0) )
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
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,(
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

fof(f34,plain,(
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
      & v4_orders_2(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

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
      & v4_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

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
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
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
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
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

fof(f910,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_114 ),
    inference(avatar_component_clause,[],[f909])).

fof(f1081,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_35
    | ~ spl7_135 ),
    inference(avatar_split_clause,[],[f1065,f1059,f340,f99,f89])).

fof(f89,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f99,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f340,plain,
    ( spl7_35
  <=> ! [X1,X0] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1059,plain,
    ( spl7_135
  <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1065,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_35
    | ~ spl7_135 ),
    inference(resolution,[],[f1060,f341])).

fof(f341,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f340])).

fof(f1060,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_135 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1061,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | spl7_12
    | ~ spl7_29
    | spl7_135
    | ~ spl7_6
    | ~ spl7_115 ),
    inference(avatar_split_clause,[],[f1023,f912,f111,f1059,f262,f151,f271,f268])).

fof(f262,plain,
    ( spl7_29
  <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f111,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f912,plain,
    ( spl7_115
  <=> ! [X5] :
        ( r1_lattice3(sK0,X5,sK3)
        | ~ r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f1023,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_6
    | ~ spl7_115 ),
    inference(resolution,[],[f913,f302])).

fof(f302,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,k2_yellow_0(sK0,X1))
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ v1_finset_1(X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f300,f54])).

fof(f54,plain,(
    ! [X7] :
      ( r2_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f87,f112])).

fof(f112,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f913,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X5,sK3) )
    | ~ spl7_115 ),
    inference(avatar_component_clause,[],[f912])).

fof(f1034,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | spl7_12
    | ~ spl7_4
    | spl7_29 ),
    inference(avatar_split_clause,[],[f1032,f262,f103,f151,f271,f268])).

fof(f1032,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_29 ),
    inference(resolution,[],[f915,f59])).

fof(f915,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_29 ),
    inference(resolution,[],[f263,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f263,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | spl7_29 ),
    inference(avatar_component_clause,[],[f262])).

fof(f914,plain,
    ( spl7_114
    | spl7_115
    | ~ spl7_2
    | ~ spl7_28
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f897,f456,f257,f92,f912,f909])).

fof(f92,plain,
    ( spl7_2
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f257,plain,
    ( spl7_28
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f456,plain,
    ( spl7_47
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ r2_hidden(X1,X2)
        | ~ r1_lattice3(sK0,X2,sK3)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f897,plain,
    ( ! [X6,X5] :
        ( ~ r1_lattice3(sK0,sK2,sK3)
        | r1_lattice3(sK0,X5,sK3)
        | ~ r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6) )
    | ~ spl7_28
    | ~ spl7_47 ),
    inference(resolution,[],[f258,f474])).

fof(f474,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_lattice3(sK0,X1,sK3)
        | r1_lattice3(sK0,X2,sK3)
        | ~ r1_lattice3(sK0,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X3) )
    | ~ spl7_47 ),
    inference(resolution,[],[f457,f85])).

fof(f457,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ r1_lattice3(sK0,X2,sK3)
        | r1_lattice3(sK0,X0,sK3)
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f456])).

fof(f258,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f257])).

fof(f870,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_6
    | spl7_32 ),
    inference(avatar_split_clause,[],[f282,f279,f111,f99,f89])).

fof(f279,plain,
    ( spl7_32
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f282,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_6
    | spl7_32 ),
    inference(resolution,[],[f280,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f79,f112])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f280,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f869,plain,
    ( ~ spl7_14
    | ~ spl7_24
    | ~ spl7_1
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f867,f845,f89,f231,f160])).

fof(f160,plain,
    ( spl7_14
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f231,plain,
    ( spl7_24
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f845,plain,
    ( spl7_106
  <=> ! [X0] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f867,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_106 ),
    inference(resolution,[],[f866,f56])).

fof(f56,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f866,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_106 ),
    inference(resolution,[],[f846,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f846,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f845])).

fof(f864,plain,
    ( ~ spl7_6
    | ~ spl7_3
    | spl7_2
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f851,f836,f92,f99,f111])).

fof(f836,plain,
    ( spl7_104
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f851,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_104 ),
    inference(resolution,[],[f837,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f837,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f836])).

fof(f847,plain,
    ( spl7_106
    | ~ spl7_3
    | ~ spl7_6
    | spl7_103 ),
    inference(avatar_split_clause,[],[f843,f833,f111,f99,f845])).

fof(f833,plain,
    ( spl7_103
  <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f843,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_6
    | spl7_103 ),
    inference(resolution,[],[f834,f166])).

fof(f166,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X2,X0)
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f70,f112])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f834,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_103 ),
    inference(avatar_component_clause,[],[f833])).

fof(f838,plain,
    ( ~ spl7_103
    | spl7_104
    | ~ spl7_3
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f830,f826,f99,f836,f833])).

fof(f826,plain,
    ( spl7_102
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f830,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_102 ),
    inference(resolution,[],[f827,f100])).

fof(f100,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f827,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) )
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f826])).

fof(f828,plain,
    ( ~ spl7_24
    | spl7_102
    | ~ spl7_14
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f824,f163,f111,f160,f826,f231])).

fof(f163,plain,
    ( spl7_15
  <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f824,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2) )
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f821])).

fof(f821,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(superposition,[],[f733,f164])).

fof(f164,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f733,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_yellow_0(sK0,sK4(X1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1)))
        | ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f730,f57])).

fof(f57,plain,(
    ! [X5] :
      ( r2_yellow_0(sK0,sK4(X5))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f730,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f86,f112])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f458,plain,
    ( ~ spl7_3
    | spl7_47
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f454,f439,f111,f99,f456,f99])).

fof(f439,plain,
    ( spl7_45
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f454,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ r1_lattice3(sK0,X2,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2) )
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_45 ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2) )
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_45 ),
    inference(resolution,[],[f443,f405])).

fof(f405,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f77,f112])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f443,plain,
    ( ! [X4,X5] :
        ( ~ r1_orders_2(sK0,sK3,X5)
        | ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK3) )
    | ~ spl7_3
    | ~ spl7_45 ),
    inference(resolution,[],[f440,f100])).

fof(f440,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X2)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f439])).

fof(f441,plain,
    ( ~ spl7_6
    | spl7_45
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f437,f115,f439,f111])).

fof(f115,plain,
    ( spl7_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f437,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f81,f116])).

fof(f116,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f342,plain,
    ( ~ spl7_6
    | spl7_35
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f338,f333,f340,f111])).

fof(f333,plain,
    ( spl7_34
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_34 ),
    inference(resolution,[],[f334,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( ~ spl7_6
    | spl7_34
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f330,f111,f333,f111])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f328,f80])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X0),X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f66,f112])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f281,plain,
    ( ~ spl7_32
    | spl7_31 ),
    inference(avatar_split_clause,[],[f276,f271,f279])).

fof(f276,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_31 ),
    inference(resolution,[],[f272,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f272,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f275,plain,(
    spl7_30 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl7_30 ),
    inference(resolution,[],[f269,f65])).

fof(f65,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f269,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f273,plain,
    ( ~ spl7_30
    | ~ spl7_31
    | spl7_12
    | spl7_28 ),
    inference(avatar_split_clause,[],[f266,f257,f151,f271,f268])).

fof(f266,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_28 ),
    inference(resolution,[],[f264,f59])).

fof(f264,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f257])).

fof(f240,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_24 ),
    inference(avatar_split_clause,[],[f239,f231,f111,f99,f92])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_6
    | spl7_24 ),
    inference(resolution,[],[f237,f132])).

fof(f237,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f182,plain,
    ( ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f176,f151,f119])).

fof(f119,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f176,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_12 ),
    inference(superposition,[],[f64,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f170,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6
    | spl7_14 ),
    inference(avatar_split_clause,[],[f168,f160,f111,f103,f99,f92])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_6
    | spl7_14 ),
    inference(resolution,[],[f167,f132])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_14 ),
    inference(resolution,[],[f161,f85])).

fof(f161,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f165,plain,
    ( ~ spl7_14
    | spl7_15
    | ~ spl7_3
    | spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f158,f111,f92,f99,f163,f160])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f93,f133])).

fof(f133,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK6(sK0,sK2,X0) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,X0)))
        | ~ m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f132,f58])).

fof(f58,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | k2_yellow_0(sK0,sK4(X5)) = X5
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f121,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f63,f119])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f117,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f50,f115])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f60,f99])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f61,f92,f89])).

fof(f61,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f62,f92,f89])).

fof(f62,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (24491)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.44  % (24499)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (24502)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (24493)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (24487)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (24488)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (24496)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (24485)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (24486)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24490)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (24497)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24500)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (24495)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (24501)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (24492)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (24504)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (24489)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (24494)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (24503)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (24505)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (24498)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (24491)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1223,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f94,f97,f101,f105,f113,f117,f121,f165,f170,f182,f240,f273,f275,f281,f335,f342,f441,f458,f828,f838,f847,f864,f869,f870,f914,f1034,f1061,f1081,f1222])).
% 0.21/0.51  fof(f1222,plain,(
% 0.21/0.51    ~spl7_30 | ~spl7_31 | spl7_12 | ~spl7_4 | ~spl7_114),
% 0.21/0.51    inference(avatar_split_clause,[],[f1220,f909,f103,f151,f271,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    spl7_30 <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    spl7_31 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl7_12 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f909,plain,(
% 0.21/0.51    spl7_114 <=> ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).
% 0.21/0.51  fof(f1220,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | ~spl7_114),
% 0.21/0.51    inference(resolution,[],[f910,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ((((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f39,f38,f37,f36,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 0.21/0.51    inference(rectify,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).
% 0.21/0.51  fof(f910,plain,(
% 0.21/0.51    ( ! [X6] : (~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_114),
% 0.21/0.51    inference(avatar_component_clause,[],[f909])).
% 0.21/0.51  fof(f1081,plain,(
% 0.21/0.51    spl7_1 | ~spl7_3 | ~spl7_35 | ~spl7_135),
% 0.21/0.51    inference(avatar_split_clause,[],[f1065,f1059,f340,f99,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl7_1 <=> r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl7_3 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    spl7_35 <=> ! [X1,X0] : (r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.51  fof(f1059,plain,(
% 0.21/0.51    spl7_135 <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).
% 0.21/0.51  fof(f1065,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3) | (~spl7_35 | ~spl7_135)),
% 0.21/0.51    inference(resolution,[],[f1060,f341])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f340])).
% 0.21/0.51  fof(f1060,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | ~spl7_135),
% 0.21/0.51    inference(avatar_component_clause,[],[f1059])).
% 0.21/0.51  fof(f1061,plain,(
% 0.21/0.51    ~spl7_30 | ~spl7_31 | spl7_12 | ~spl7_29 | spl7_135 | ~spl7_6 | ~spl7_115),
% 0.21/0.51    inference(avatar_split_clause,[],[f1023,f912,f111,f1059,f262,f151,f271,f268])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl7_29 <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl7_6 <=> l1_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f912,plain,(
% 0.21/0.51    spl7_115 <=> ! [X5] : (r1_lattice3(sK0,X5,sK3) | ~r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 0.21/0.51  fof(f1023,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_6 | ~spl7_115)),
% 0.21/0.51    inference(resolution,[],[f913,f302])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    ( ! [X1] : (r1_lattice3(sK0,X1,k2_yellow_0(sK0,X1)) | ~m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~v1_finset_1(X1)) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f300,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_yellow_0(sK0,X0) | ~m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,k2_yellow_0(sK0,X0))) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f87,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    l1_orders_2(sK0) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 0.21/0.51  fof(f913,plain,(
% 0.21/0.51    ( ! [X5] : (~r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X5,sK3)) ) | ~spl7_115),
% 0.21/0.51    inference(avatar_component_clause,[],[f912])).
% 0.21/0.51  fof(f1034,plain,(
% 0.21/0.51    ~spl7_30 | ~spl7_31 | spl7_12 | ~spl7_4 | spl7_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f1032,f262,f103,f151,f271,f268])).
% 0.21/0.51  fof(f1032,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_29),
% 0.21/0.51    inference(resolution,[],[f915,f59])).
% 0.21/0.51  fof(f915,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl7_29),
% 0.21/0.51    inference(resolution,[],[f263,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | spl7_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f262])).
% 0.21/0.51  fof(f914,plain,(
% 0.21/0.51    spl7_114 | spl7_115 | ~spl7_2 | ~spl7_28 | ~spl7_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f897,f456,f257,f92,f912,f909])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl7_2 <=> r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    spl7_28 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.51  fof(f456,plain,(
% 0.21/0.51    spl7_47 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,X0,X1) | ~r2_hidden(X1,X2) | ~r1_lattice3(sK0,X2,sK3) | r1_lattice3(sK0,X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.21/0.51  fof(f897,plain,(
% 0.21/0.51    ( ! [X6,X5] : (~r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,X5,sK3) | ~r1_lattice3(sK0,X5,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X6)) ) | (~spl7_28 | ~spl7_47)),
% 0.21/0.51    inference(resolution,[],[f258,f474])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~r1_lattice3(sK0,X1,sK3) | r1_lattice3(sK0,X2,sK3) | ~r1_lattice3(sK0,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X3)) ) | ~spl7_47),
% 0.21/0.51    inference(resolution,[],[f457,f85])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~r1_lattice3(sK0,X2,sK3) | r1_lattice3(sK0,X0,sK3) | ~r1_lattice3(sK0,X0,X1)) ) | ~spl7_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f456])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f257])).
% 0.21/0.51  fof(f870,plain,(
% 0.21/0.51    spl7_1 | ~spl7_3 | ~spl7_6 | spl7_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f282,f279,f111,f99,f89])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    spl7_32 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3) | (~spl7_6 | spl7_32)),
% 0.21/0.51    inference(resolution,[],[f280,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f79,f112])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f279])).
% 0.21/0.51  fof(f869,plain,(
% 0.21/0.51    ~spl7_14 | ~spl7_24 | ~spl7_1 | ~spl7_106),
% 0.21/0.51    inference(avatar_split_clause,[],[f867,f845,f89,f231,f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl7_14 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl7_24 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.51  fof(f845,plain,(
% 0.21/0.51    spl7_106 <=> ! [X0] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 0.21/0.51  fof(f867,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_106),
% 0.21/0.51    inference(resolution,[],[f866,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f866,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0)) | ~r1_lattice3(sK0,X0,sK3)) ) | ~spl7_106),
% 0.21/0.51    inference(resolution,[],[f846,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f846,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3)) ) | ~spl7_106),
% 0.21/0.51    inference(avatar_component_clause,[],[f845])).
% 0.21/0.51  fof(f864,plain,(
% 0.21/0.51    ~spl7_6 | ~spl7_3 | spl7_2 | ~spl7_104),
% 0.21/0.51    inference(avatar_split_clause,[],[f851,f836,f92,f99,f111])).
% 0.21/0.51  fof(f836,plain,(
% 0.21/0.51    spl7_104 <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 0.21/0.51  fof(f851,plain,(
% 0.21/0.51    r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl7_104),
% 0.21/0.51    inference(resolution,[],[f837,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f837,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | ~spl7_104),
% 0.21/0.51    inference(avatar_component_clause,[],[f836])).
% 0.21/0.51  fof(f847,plain,(
% 0.21/0.51    spl7_106 | ~spl7_3 | ~spl7_6 | spl7_103),
% 0.21/0.51    inference(avatar_split_clause,[],[f843,f833,f111,f99,f845])).
% 0.21/0.51  fof(f833,plain,(
% 0.21/0.51    spl7_103 <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 0.21/0.51  fof(f843,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3)) ) | (~spl7_6 | spl7_103)),
% 0.21/0.51    inference(resolution,[],[f834,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattice3(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X2,X0) | ~r1_lattice3(sK0,X0,X1)) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f70,f112])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r1_lattice3(X0,X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_103),
% 0.21/0.51    inference(avatar_component_clause,[],[f833])).
% 0.21/0.51  fof(f838,plain,(
% 0.21/0.51    ~spl7_103 | spl7_104 | ~spl7_3 | ~spl7_102),
% 0.21/0.51    inference(avatar_split_clause,[],[f830,f826,f99,f836,f833])).
% 0.21/0.51  fof(f826,plain,(
% 0.21/0.51    spl7_102 <=> ! [X0] : (~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 0.21/0.51  fof(f830,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl7_3 | ~spl7_102)),
% 0.21/0.51    inference(resolution,[],[f827,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f827,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)) ) | ~spl7_102),
% 0.21/0.51    inference(avatar_component_clause,[],[f826])).
% 0.21/0.51  fof(f828,plain,(
% 0.21/0.51    ~spl7_24 | spl7_102 | ~spl7_14 | ~spl7_6 | ~spl7_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f824,f163,f111,f160,f826,f231])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl7_15 <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f824,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3)) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2)) ) | (~spl7_6 | ~spl7_15)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f821])).
% 0.21/0.51  fof(f821,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3)) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_15)),
% 0.21/0.51    inference(superposition,[],[f733,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f733,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k2_yellow_0(sK0,sK4(X1)),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1))) | ~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f730,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X5] : (r2_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f730,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))) ) | ~spl7_6),
% 0.21/0.51    inference(resolution,[],[f86,f112])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    ~spl7_3 | spl7_47 | ~spl7_3 | ~spl7_6 | ~spl7_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f454,f439,f111,f99,f456,f99])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    spl7_45 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,X0,X1) | r1_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.51  fof(f454,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK3) | ~r1_lattice3(sK0,X2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_hidden(X1,X2)) ) | (~spl7_3 | ~spl7_6 | ~spl7_45)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f449])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_hidden(X1,X2)) ) | (~spl7_3 | ~spl7_6 | ~spl7_45)),
% 0.21/0.52    inference(resolution,[],[f443,f405])).
% 0.21/0.52  fof(f405,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) ) | ~spl7_6),
% 0.21/0.52    inference(resolution,[],[f77,f112])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r1_orders_2(sK0,sK3,X5) | ~r1_lattice3(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r1_lattice3(sK0,X4,sK3)) ) | (~spl7_3 | ~spl7_45)),
% 0.21/0.52    inference(resolution,[],[f440,f100])).
% 0.21/0.52  fof(f440,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X2) | ~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X1)) ) | ~spl7_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f439])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    ~spl7_6 | spl7_45 | ~spl7_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f437,f115,f439,f111])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl7_7 <=> v4_orders_2(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.52  fof(f437,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,X0,X2)) ) | ~spl7_7),
% 0.21/0.52    inference(resolution,[],[f81,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    v4_orders_2(sK0) | ~spl7_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f115])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    ~spl7_6 | spl7_35 | ~spl7_34),
% 0.21/0.52    inference(avatar_split_clause,[],[f338,f333,f340,f111])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    spl7_34 <=> ! [X1,X0] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl7_34),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f336])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl7_34),
% 0.21/0.52    inference(resolution,[],[f334,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f333])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ~spl7_6 | spl7_34 | ~spl7_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f330,f111,f333,f111])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f329])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 0.21/0.52    inference(resolution,[],[f328,f80])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(X0),X1)) ) | ~spl7_6),
% 0.21/0.52    inference(resolution,[],[f66,f112])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~spl7_32 | spl7_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f276,f271,f279])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_31),
% 0.21/0.52    inference(resolution,[],[f272,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl7_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f271])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    spl7_30),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f274])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    $false | spl7_30),
% 0.21/0.52    inference(resolution,[],[f269,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f268])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    ~spl7_30 | ~spl7_31 | spl7_12 | spl7_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f266,f257,f151,f271,f268])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_28),
% 0.21/0.52    inference(resolution,[],[f264,f59])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl7_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f257])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | ~spl7_6 | spl7_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f239,f231,f111,f99,f92])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_6 | spl7_24)),
% 0.21/0.52    inference(resolution,[],[f237,f132])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | spl7_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f231])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ~spl7_8 | ~spl7_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f176,f151,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl7_12),
% 0.21/0.52    inference(superposition,[],[f64,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6 | spl7_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f168,f160,f111,f103,f99,f92])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_6 | spl7_14)),
% 0.21/0.52    inference(resolution,[],[f167,f132])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK6(sK0,sK2,sK3),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl7_14),
% 0.21/0.52    inference(resolution,[],[f161,f85])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f160])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl7_14 | spl7_15 | ~spl7_3 | spl7_2 | ~spl7_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f158,f111,f92,f99,f163,f160])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,u1_struct_0(sK0)) | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (spl7_2 | ~spl7_6)),
% 0.21/0.52    inference(resolution,[],[f93,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X0] : (r1_lattice3(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK6(sK0,sK2,X0) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,X0))) | ~m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0))) ) | ~spl7_6),
% 0.21/0.52    inference(resolution,[],[f132,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X5] : (~r2_hidden(X5,sK2) | k2_yellow_0(sK0,sK4(X5)) = X5 | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~r1_lattice3(sK0,sK2,sK3) | spl7_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl7_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f63,f119])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl7_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f115])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v4_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl7_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f111])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    l1_orders_2(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl7_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f103])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f60,f99])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl7_1 | spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f61,f92,f89])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~spl7_1 | ~spl7_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f92,f89])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (24491)------------------------------
% 0.21/0.52  % (24491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24491)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24491)Memory used [KB]: 11641
% 0.21/0.52  % (24491)Time elapsed: 0.123 s
% 0.21/0.52  % (24491)------------------------------
% 0.21/0.52  % (24491)------------------------------
% 0.21/0.52  % (24480)Success in time 0.163 s
%------------------------------------------------------------------------------
