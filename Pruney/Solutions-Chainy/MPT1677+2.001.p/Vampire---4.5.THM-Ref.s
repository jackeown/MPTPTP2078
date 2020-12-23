%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:17 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 546 expanded)
%              Number of leaves         :   49 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          : 1152 (5758 expanded)
%              Number of equality atoms :   76 ( 622 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f101,f105,f109,f117,f121,f125,f158,f177,f227,f229,f234,f243,f254,f286,f292,f323,f421,f635,f646,f656,f664,f680,f696,f764,f852,f865,f930,f1089,f1091,f1094])).

fof(f1094,plain,
    ( ~ spl7_3
    | ~ spl7_80
    | spl7_1
    | ~ spl7_45
    | ~ spl7_145 ),
    inference(avatar_split_clause,[],[f1092,f1087,f419,f93,f688,f103])).

fof(f103,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f688,plain,
    ( spl7_80
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f93,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f419,plain,
    ( spl7_45
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1087,plain,
    ( spl7_145
  <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f1092,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_45
    | ~ spl7_145 ),
    inference(resolution,[],[f1088,f420])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f419])).

fof(f1088,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_145 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1091,plain,
    ( ~ spl7_21
    | ~ spl7_22
    | spl7_10
    | spl7_144 ),
    inference(avatar_split_clause,[],[f1090,f1084,f162,f225,f222])).

fof(f222,plain,
    ( spl7_21
  <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f225,plain,
    ( spl7_22
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f162,plain,
    ( spl7_10
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1084,plain,
    ( spl7_144
  <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f1090,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_144 ),
    inference(resolution,[],[f1085,f55])).

fof(f55,plain,(
    ! [X7] :
      ( r2_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
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
    & v4_orders_2(sK0) ),
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
      & v4_orders_2(X0) ) ),
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
      & v4_orders_2(X0) ) ),
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
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f1085,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_144 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1089,plain,
    ( ~ spl7_6
    | ~ spl7_144
    | spl7_145
    | ~ spl7_119 ),
    inference(avatar_split_clause,[],[f1066,f928,f1087,f1084,f115])).

fof(f115,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f928,plain,
    ( spl7_119
  <=> ! [X12] :
        ( r1_lattice3(sK0,X12,sK3)
        | ~ r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f1066,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ l1_orders_2(sK0)
    | ~ spl7_119 ),
    inference(resolution,[],[f929,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f91,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f929,plain,
    ( ! [X12] :
        ( ~ r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X12,sK3) )
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f928])).

fof(f930,plain,
    ( ~ spl7_20
    | ~ spl7_3
    | spl7_119
    | ~ spl7_79
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f910,f863,f678,f928,f103,f216])).

fof(f216,plain,
    ( spl7_20
  <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f678,plain,
    ( spl7_79
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f863,plain,
    ( spl7_106
  <=> r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f910,plain,
    ( ! [X12] :
        ( r1_lattice3(sK0,X12,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) )
    | ~ spl7_79
    | ~ spl7_106 ),
    inference(resolution,[],[f679,f864])).

fof(f864,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f863])).

fof(f679,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,X1)
        | r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f678])).

fof(f865,plain,
    ( spl7_106
    | ~ spl7_20
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_105 ),
    inference(avatar_split_clause,[],[f853,f850,f115,f103,f216,f863])).

fof(f850,plain,
    ( spl7_105
  <=> r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f853,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_6
    | ~ spl7_105 ),
    inference(resolution,[],[f851,f440])).

fof(f440,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,k1_tarski(X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f69,f116])).

fof(f116,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f851,plain,
    ( r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_105 ),
    inference(avatar_component_clause,[],[f850])).

fof(f852,plain,
    ( ~ spl7_3
    | spl7_105
    | ~ spl7_2
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f843,f762,f96,f850,f103])).

fof(f96,plain,
    ( spl7_2
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f762,plain,
    ( spl7_92
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | ~ r1_lattice3(sK0,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f843,plain,
    ( r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_92 ),
    inference(resolution,[],[f763,f100])).

fof(f100,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f763,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,sK2,X1)
        | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f762])).

fof(f764,plain,
    ( ~ spl7_20
    | spl7_92
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f751,f203,f115,f762,f216])).

fof(f203,plain,
    ( spl7_17
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f751,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK2,X1)
        | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) )
    | ~ spl7_6
    | ~ spl7_17 ),
    inference(resolution,[],[f204,f514])).

fof(f514,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,X0)
        | r2_lattice3(sK0,k1_tarski(X0),X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f505,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f505,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(k1_tarski(X2),X4)
        | r2_lattice3(sK0,k1_tarski(X3),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,X3) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X3),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_tarski(k1_tarski(X2),X4)
        | ~ r1_lattice3(sK0,X4,X3) )
    | ~ spl7_6 ),
    inference(resolution,[],[f499,f269])).

fof(f269,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X2,X0)
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f71,f116])).

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f499,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X1),X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f497,f415])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X0),X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f67,f116])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X0),X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f70,f116])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f204,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f696,plain,
    ( ~ spl7_6
    | ~ spl7_3
    | spl7_1
    | spl7_80 ),
    inference(avatar_split_clause,[],[f695,f688,f93,f103,f115])).

fof(f695,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_80 ),
    inference(resolution,[],[f689,f79])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f689,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_80 ),
    inference(avatar_component_clause,[],[f688])).

fof(f680,plain,
    ( ~ spl7_6
    | spl7_79
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f676,f119,f678,f115])).

fof(f119,plain,
    ( spl7_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f676,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f82,f120])).

fof(f120,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f664,plain,
    ( ~ spl7_26
    | ~ spl7_24
    | ~ spl7_1
    | ~ spl7_75 ),
    inference(avatar_split_clause,[],[f662,f654,f93,f241,f274])).

fof(f274,plain,
    ( spl7_26
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f241,plain,
    ( spl7_24
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f654,plain,
    ( spl7_75
  <=> ! [X0] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f662,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_75 ),
    inference(resolution,[],[f661,f57])).

fof(f57,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f661,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_75 ),
    inference(resolution,[],[f655,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f655,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f654])).

fof(f656,plain,
    ( spl7_75
    | ~ spl7_3
    | ~ spl7_6
    | spl7_73 ),
    inference(avatar_split_clause,[],[f651,f643,f115,f103,f654])).

fof(f643,plain,
    ( spl7_73
  <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_6
    | spl7_73 ),
    inference(resolution,[],[f644,f269])).

fof(f644,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_73 ),
    inference(avatar_component_clause,[],[f643])).

fof(f646,plain,
    ( ~ spl7_6
    | spl7_2
    | ~ spl7_73
    | ~ spl7_3
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f640,f633,f103,f643,f96,f115])).

fof(f633,plain,
    ( spl7_72
  <=> ! [X2] :
        ( r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f640,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl7_72 ),
    inference(duplicate_literal_removal,[],[f637])).

fof(f637,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_72 ),
    inference(resolution,[],[f634,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f634,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) )
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f633])).

fof(f635,plain,
    ( ~ spl7_26
    | spl7_72
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f631,f284,f241,f115,f633,f274])).

fof(f284,plain,
    ( spl7_29
  <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f631,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f629,f285])).

fof(f285,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f284])).

fof(f629,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2)
        | r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(resolution,[],[f593,f242])).

fof(f242,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f241])).

fof(f593,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r1_lattice3(sK0,sK4(X1),X0)
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f581,f58])).

fof(f58,plain,(
    ! [X5] :
      ( r2_yellow_0(sK0,sK4(X5))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f581,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f127,f116])).

fof(f127,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f90,f84])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
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

fof(f421,plain,
    ( ~ spl7_6
    | spl7_45
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f417,f115,f419,f115])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f415,f81])).

fof(f323,plain,
    ( ~ spl7_9
    | spl7_23 ),
    inference(avatar_split_clause,[],[f235,f232,f155])).

fof(f155,plain,
    ( spl7_9
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f232,plain,
    ( spl7_23
  <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f235,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_23 ),
    inference(resolution,[],[f233,f86])).

fof(f233,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f232])).

fof(f292,plain,
    ( ~ spl7_4
    | ~ spl7_24
    | spl7_26 ),
    inference(avatar_split_clause,[],[f291,f274,f241,f107])).

fof(f107,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_24
    | spl7_26 ),
    inference(resolution,[],[f272,f275])).

fof(f275,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f272,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK0,sK2,sK3),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl7_24 ),
    inference(resolution,[],[f242,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f286,plain,
    ( ~ spl7_26
    | spl7_29
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f271,f241,f284,f274])).

fof(f271,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_24 ),
    inference(resolution,[],[f242,f59])).

fof(f59,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | k2_yellow_0(sK0,sK4(X5)) = X5
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f254,plain,
    ( ~ spl7_6
    | spl7_20 ),
    inference(avatar_split_clause,[],[f252,f216,f115])).

fof(f252,plain,
    ( ~ l1_orders_2(sK0)
    | spl7_20 ),
    inference(resolution,[],[f217,f84])).

fof(f217,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f216])).

fof(f243,plain,
    ( spl7_24
    | ~ spl7_3
    | spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f239,f115,f96,f103,f241])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f97,f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0,X1),X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f116])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f234,plain,
    ( ~ spl7_23
    | spl7_22 ),
    inference(avatar_split_clause,[],[f230,f225,f232])).

fof(f230,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | spl7_22 ),
    inference(resolution,[],[f226,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f226,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f229,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f223,f66])).

fof(f66,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f223,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f222])).

fof(f227,plain,
    ( ~ spl7_21
    | ~ spl7_22
    | spl7_10
    | spl7_17 ),
    inference(avatar_split_clause,[],[f220,f203,f162,f225,f222])).

fof(f220,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_17 ),
    inference(resolution,[],[f218,f60])).

fof(f60,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f218,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f177,plain,
    ( ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f168,f162,f123])).

fof(f123,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f168,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_10 ),
    inference(superposition,[],[f65,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f158,plain,
    ( spl7_9
    | ~ spl7_3
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f153,f115,f93,f103,f155])).

fof(f153,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_1
    | ~ spl7_6 ),
    inference(resolution,[],[f152,f94])).

fof(f94,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f125,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f64,f123])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f121,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f51,f119])).

fof(f51,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f117,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f115])).

fof(f52,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f61,f103])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f62,f96,f93])).

fof(f62,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f63,f96,f93])).

fof(f63,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:18:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (22207)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (22191)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (22196)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (22188)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (22199)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22200)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (22187)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (22198)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (22203)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (22186)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (22194)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (22201)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (22195)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (22202)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (22206)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (22197)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (22190)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (22192)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (22189)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (22205)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (22204)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.63/0.56  % (22192)Refutation found. Thanks to Tanya!
% 1.63/0.56  % SZS status Theorem for theBenchmark
% 1.63/0.56  % SZS output start Proof for theBenchmark
% 1.63/0.56  fof(f1096,plain,(
% 1.63/0.56    $false),
% 1.63/0.56    inference(avatar_sat_refutation,[],[f98,f101,f105,f109,f117,f121,f125,f158,f177,f227,f229,f234,f243,f254,f286,f292,f323,f421,f635,f646,f656,f664,f680,f696,f764,f852,f865,f930,f1089,f1091,f1094])).
% 1.63/0.56  fof(f1094,plain,(
% 1.63/0.56    ~spl7_3 | ~spl7_80 | spl7_1 | ~spl7_45 | ~spl7_145),
% 1.63/0.56    inference(avatar_split_clause,[],[f1092,f1087,f419,f93,f688,f103])).
% 1.63/0.56  fof(f103,plain,(
% 1.63/0.56    spl7_3 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.63/0.56  fof(f688,plain,(
% 1.63/0.56    spl7_80 <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 1.63/0.56  fof(f93,plain,(
% 1.63/0.56    spl7_1 <=> r1_lattice3(sK0,sK1,sK3)),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.63/0.56  fof(f419,plain,(
% 1.63/0.56    spl7_45 <=> ! [X1,X0] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.63/0.56  fof(f1087,plain,(
% 1.63/0.56    spl7_145 <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).
% 1.63/0.56  fof(f1092,plain,(
% 1.63/0.56    r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_45 | ~spl7_145)),
% 1.63/0.56    inference(resolution,[],[f1088,f420])).
% 1.63/0.56  fof(f420,plain,(
% 1.63/0.56    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_45),
% 1.63/0.56    inference(avatar_component_clause,[],[f419])).
% 1.63/0.56  fof(f1088,plain,(
% 1.63/0.56    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | ~spl7_145),
% 1.63/0.56    inference(avatar_component_clause,[],[f1087])).
% 1.63/0.56  fof(f1091,plain,(
% 1.63/0.56    ~spl7_21 | ~spl7_22 | spl7_10 | spl7_144),
% 1.63/0.56    inference(avatar_split_clause,[],[f1090,f1084,f162,f225,f222])).
% 1.63/0.56  fof(f222,plain,(
% 1.63/0.56    spl7_21 <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.63/0.56  fof(f225,plain,(
% 1.63/0.56    spl7_22 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.63/0.56  fof(f162,plain,(
% 1.63/0.56    spl7_10 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.63/0.56  fof(f1084,plain,(
% 1.63/0.56    spl7_144 <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).
% 1.63/0.56  fof(f1090,plain,(
% 1.63/0.56    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_144),
% 1.63/0.56    inference(resolution,[],[f1085,f55])).
% 1.63/0.56  fof(f55,plain,(
% 1.63/0.56    ( ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f39])).
% 1.63/0.56  fof(f39,plain,(
% 1.63/0.56    ((((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 1.63/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f38,f37,f36,f35,f34])).
% 1.63/0.56  fof(f34,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f35,plain,(
% 1.63/0.56    ? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f36,plain,(
% 1.63/0.56    ? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f37,plain,(
% 1.63/0.56    ? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f38,plain,(
% 1.63/0.56    ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f33,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 1.63/0.56    inference(rectify,[],[f32])).
% 1.63/0.56  fof(f32,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 1.63/0.56    inference(flattening,[],[f31])).
% 1.63/0.56  fof(f31,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 1.63/0.56    inference(nnf_transformation,[],[f19])).
% 1.63/0.56  fof(f19,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 1.63/0.56    inference(flattening,[],[f18])).
% 1.63/0.56  fof(f18,plain,(
% 1.63/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 1.63/0.56    inference(ennf_transformation,[],[f17])).
% 1.63/0.56  fof(f17,plain,(
% 1.63/0.56    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.63/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.63/0.56  fof(f16,plain,(
% 1.63/0.56    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.63/0.56    inference(pure_predicate_removal,[],[f15])).
% 1.63/0.57  fof(f15,plain,(
% 1.63/0.57    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.63/0.57    inference(rectify,[],[f14])).
% 1.63/0.57  fof(f14,negated_conjecture,(
% 1.63/0.57    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.63/0.57    inference(negated_conjecture,[],[f13])).
% 1.63/0.57  fof(f13,conjecture,(
% 1.63/0.57    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).
% 1.63/0.57  fof(f1085,plain,(
% 1.63/0.57    ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl7_144),
% 1.63/0.57    inference(avatar_component_clause,[],[f1084])).
% 1.63/0.57  fof(f1089,plain,(
% 1.63/0.57    ~spl7_6 | ~spl7_144 | spl7_145 | ~spl7_119),
% 1.63/0.57    inference(avatar_split_clause,[],[f1066,f928,f1087,f1084,f115])).
% 1.63/0.57  fof(f115,plain,(
% 1.63/0.57    spl7_6 <=> l1_orders_2(sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.63/0.57  fof(f928,plain,(
% 1.63/0.57    spl7_119 <=> ! [X12] : (r1_lattice3(sK0,X12,sK3) | ~r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).
% 1.63/0.57  fof(f1066,plain,(
% 1.63/0.57    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~l1_orders_2(sK0) | ~spl7_119),
% 1.63/0.57    inference(resolution,[],[f929,f126])).
% 1.63/0.57  fof(f126,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f91,f84])).
% 1.63/0.57  fof(f84,plain,(
% 1.63/0.57    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f28])).
% 1.63/0.57  fof(f28,plain,(
% 1.63/0.57    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f9])).
% 1.63/0.57  fof(f9,axiom,(
% 1.63/0.57    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).
% 1.63/0.57  fof(f91,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(equality_resolution,[],[f73])).
% 1.63/0.57  fof(f73,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f44])).
% 1.63/0.57  fof(f44,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 1.63/0.57  fof(f43,plain,(
% 1.63/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f42,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(rectify,[],[f41])).
% 1.63/0.57  fof(f41,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(flattening,[],[f40])).
% 1.63/0.57  fof(f40,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(nnf_transformation,[],[f23])).
% 1.63/0.57  fof(f23,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(flattening,[],[f22])).
% 1.63/0.57  fof(f22,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f8])).
% 1.63/0.57  fof(f8,axiom,(
% 1.63/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).
% 1.63/0.57  fof(f929,plain,(
% 1.63/0.57    ( ! [X12] : (~r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X12,sK3)) ) | ~spl7_119),
% 1.63/0.57    inference(avatar_component_clause,[],[f928])).
% 1.63/0.57  fof(f930,plain,(
% 1.63/0.57    ~spl7_20 | ~spl7_3 | spl7_119 | ~spl7_79 | ~spl7_106),
% 1.63/0.57    inference(avatar_split_clause,[],[f910,f863,f678,f928,f103,f216])).
% 1.63/0.57  fof(f216,plain,(
% 1.63/0.57    spl7_20 <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.63/0.57  fof(f678,plain,(
% 1.63/0.57    spl7_79 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,X0,X1) | r1_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 1.63/0.57  fof(f863,plain,(
% 1.63/0.57    spl7_106 <=> r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 1.63/0.57  fof(f910,plain,(
% 1.63/0.57    ( ! [X12] : (r1_lattice3(sK0,X12,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X12,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))) ) | (~spl7_79 | ~spl7_106)),
% 1.63/0.57    inference(resolution,[],[f679,f864])).
% 1.63/0.57  fof(f864,plain,(
% 1.63/0.57    r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~spl7_106),
% 1.63/0.57    inference(avatar_component_clause,[],[f863])).
% 1.63/0.57  fof(f679,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X2,X1) | r1_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1)) ) | ~spl7_79),
% 1.63/0.57    inference(avatar_component_clause,[],[f678])).
% 1.63/0.57  fof(f865,plain,(
% 1.63/0.57    spl7_106 | ~spl7_20 | ~spl7_3 | ~spl7_6 | ~spl7_105),
% 1.63/0.57    inference(avatar_split_clause,[],[f853,f850,f115,f103,f216,f863])).
% 1.63/0.57  fof(f850,plain,(
% 1.63/0.57    spl7_105 <=> r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 1.63/0.57  fof(f853,plain,(
% 1.63/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | (~spl7_6 | ~spl7_105)),
% 1.63/0.57    inference(resolution,[],[f851,f440])).
% 1.63/0.57  fof(f440,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_lattice3(sK0,k1_tarski(X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f69,f116])).
% 1.63/0.57  fof(f116,plain,(
% 1.63/0.57    l1_orders_2(sK0) | ~spl7_6),
% 1.63/0.57    inference(avatar_component_clause,[],[f115])).
% 1.63/0.57  fof(f69,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X2,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f20])).
% 1.63/0.57  fof(f20,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f11])).
% 1.63/0.57  fof(f11,axiom,(
% 1.63/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.63/0.57  fof(f851,plain,(
% 1.63/0.57    r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~spl7_105),
% 1.63/0.57    inference(avatar_component_clause,[],[f850])).
% 1.63/0.57  fof(f852,plain,(
% 1.63/0.57    ~spl7_3 | spl7_105 | ~spl7_2 | ~spl7_92),
% 1.63/0.57    inference(avatar_split_clause,[],[f843,f762,f96,f850,f103])).
% 1.63/0.57  fof(f96,plain,(
% 1.63/0.57    spl7_2 <=> r1_lattice3(sK0,sK2,sK3)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.63/0.57  fof(f762,plain,(
% 1.63/0.57    spl7_92 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~r1_lattice3(sK0,sK2,X1))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 1.63/0.57  fof(f843,plain,(
% 1.63/0.57    r2_lattice3(sK0,k1_tarski(sK3),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_2 | ~spl7_92)),
% 1.63/0.57    inference(resolution,[],[f763,f100])).
% 1.63/0.57  fof(f100,plain,(
% 1.63/0.57    r1_lattice3(sK0,sK2,sK3) | ~spl7_2),
% 1.63/0.57    inference(avatar_component_clause,[],[f96])).
% 1.63/0.57  fof(f763,plain,(
% 1.63/0.57    ( ! [X1] : (~r1_lattice3(sK0,sK2,X1) | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_92),
% 1.63/0.57    inference(avatar_component_clause,[],[f762])).
% 1.63/0.57  fof(f764,plain,(
% 1.63/0.57    ~spl7_20 | spl7_92 | ~spl7_6 | ~spl7_17),
% 1.63/0.57    inference(avatar_split_clause,[],[f751,f203,f115,f762,f216])).
% 1.63/0.57  fof(f203,plain,(
% 1.63/0.57    spl7_17 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.63/0.57  fof(f751,plain,(
% 1.63/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK2,X1) | r2_lattice3(sK0,k1_tarski(X1),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))) ) | (~spl7_6 | ~spl7_17)),
% 1.63/0.57    inference(resolution,[],[f204,f514])).
% 1.63/0.57  fof(f514,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X2,X0) | r2_lattice3(sK0,k1_tarski(X0),X1)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f505,f86])).
% 1.63/0.57  fof(f86,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f49])).
% 1.63/0.57  fof(f49,plain,(
% 1.63/0.57    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.63/0.57    inference(nnf_transformation,[],[f3])).
% 1.63/0.57  fof(f3,axiom,(
% 1.63/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.63/0.57  fof(f505,plain,(
% 1.63/0.57    ( ! [X4,X2,X3] : (~r1_tarski(k1_tarski(X2),X4) | r2_lattice3(sK0,k1_tarski(X3),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X4,X3)) ) | ~spl7_6),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f501])).
% 1.63/0.57  fof(f501,plain,(
% 1.63/0.57    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X3),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_tarski(k1_tarski(X2),X4) | ~r1_lattice3(sK0,X4,X3)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f499,f269])).
% 1.63/0.57  fof(f269,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (r1_lattice3(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X2,X0) | ~r1_lattice3(sK0,X0,X1)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f71,f116])).
% 1.63/0.57  fof(f71,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | r1_lattice3(X0,X1,X3)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f21])).
% 1.63/0.57  fof(f21,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f12])).
% 1.63/0.57  fof(f12,axiom,(
% 1.63/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).
% 1.63/0.57  fof(f499,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_6),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f498])).
% 1.63/0.57  fof(f498,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(X1),X0)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f497,f415])).
% 1.63/0.57  fof(f415,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(X0),X1)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f67,f116])).
% 1.63/0.57  fof(f67,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f20])).
% 1.63/0.57  fof(f497,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X0),X1)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f70,f116])).
% 1.63/0.57  fof(f70,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k1_tarski(X2),X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f20])).
% 1.63/0.57  fof(f204,plain,(
% 1.63/0.57    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_17),
% 1.63/0.57    inference(avatar_component_clause,[],[f203])).
% 1.63/0.57  fof(f696,plain,(
% 1.63/0.57    ~spl7_6 | ~spl7_3 | spl7_1 | spl7_80),
% 1.63/0.57    inference(avatar_split_clause,[],[f695,f688,f93,f103,f115])).
% 1.63/0.57  fof(f695,plain,(
% 1.63/0.57    r1_lattice3(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl7_80),
% 1.63/0.57    inference(resolution,[],[f689,f79])).
% 1.63/0.57  fof(f79,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f48])).
% 1.63/0.57  fof(f48,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 1.63/0.57  fof(f47,plain,(
% 1.63/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.63/0.57    introduced(choice_axiom,[])).
% 1.63/0.57  fof(f46,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(rectify,[],[f45])).
% 1.63/0.57  fof(f45,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(nnf_transformation,[],[f25])).
% 1.63/0.57  fof(f25,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(flattening,[],[f24])).
% 1.63/0.57  fof(f24,plain,(
% 1.63/0.57    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.63/0.57    inference(ennf_transformation,[],[f7])).
% 1.63/0.57  fof(f7,axiom,(
% 1.63/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 1.63/0.57  fof(f689,plain,(
% 1.63/0.57    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | spl7_80),
% 1.63/0.57    inference(avatar_component_clause,[],[f688])).
% 1.63/0.57  fof(f680,plain,(
% 1.63/0.57    ~spl7_6 | spl7_79 | ~spl7_7),
% 1.63/0.57    inference(avatar_split_clause,[],[f676,f119,f678,f115])).
% 1.63/0.57  fof(f119,plain,(
% 1.63/0.57    spl7_7 <=> v4_orders_2(sK0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.63/0.57  fof(f676,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,X0,X2)) ) | ~spl7_7),
% 1.63/0.57    inference(resolution,[],[f82,f120])).
% 1.63/0.57  fof(f120,plain,(
% 1.63/0.57    v4_orders_2(sK0) | ~spl7_7),
% 1.63/0.57    inference(avatar_component_clause,[],[f119])).
% 1.63/0.57  fof(f82,plain,(
% 1.63/0.57    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X3,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f27])).
% 1.63/0.57  fof(f27,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 1.63/0.57    inference(flattening,[],[f26])).
% 1.63/0.57  fof(f26,plain,(
% 1.63/0.57    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 1.63/0.57    inference(ennf_transformation,[],[f10])).
% 1.63/0.57  fof(f10,axiom,(
% 1.63/0.57    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).
% 1.63/0.57  fof(f664,plain,(
% 1.63/0.57    ~spl7_26 | ~spl7_24 | ~spl7_1 | ~spl7_75),
% 1.63/0.57    inference(avatar_split_clause,[],[f662,f654,f93,f241,f274])).
% 1.63/0.57  fof(f274,plain,(
% 1.63/0.57    spl7_26 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.63/0.57  fof(f241,plain,(
% 1.63/0.57    spl7_24 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.63/0.57  fof(f654,plain,(
% 1.63/0.57    spl7_75 <=> ! [X0] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 1.63/0.57  fof(f662,plain,(
% 1.63/0.57    ~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_75),
% 1.63/0.57    inference(resolution,[],[f661,f57])).
% 1.63/0.57  fof(f57,plain,(
% 1.63/0.57    ( ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f661,plain,(
% 1.63/0.57    ( ! [X0] : (~m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0)) | ~r1_lattice3(sK0,X0,sK3)) ) | ~spl7_75),
% 1.63/0.57    inference(resolution,[],[f655,f87])).
% 1.63/0.57  fof(f87,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f50])).
% 1.63/0.57  fof(f50,plain,(
% 1.63/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.63/0.57    inference(nnf_transformation,[],[f4])).
% 1.63/0.57  fof(f4,axiom,(
% 1.63/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.57  fof(f655,plain,(
% 1.63/0.57    ( ! [X0] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3)) ) | ~spl7_75),
% 1.63/0.57    inference(avatar_component_clause,[],[f654])).
% 1.63/0.57  fof(f656,plain,(
% 1.63/0.57    spl7_75 | ~spl7_3 | ~spl7_6 | spl7_73),
% 1.63/0.57    inference(avatar_split_clause,[],[f651,f643,f115,f103,f654])).
% 1.63/0.57  fof(f643,plain,(
% 1.63/0.57    spl7_73 <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 1.63/0.57  fof(f651,plain,(
% 1.63/0.57    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_lattice3(sK0,X0,sK3)) ) | (~spl7_6 | spl7_73)),
% 1.63/0.57    inference(resolution,[],[f644,f269])).
% 1.63/0.57  fof(f644,plain,(
% 1.63/0.57    ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_73),
% 1.63/0.57    inference(avatar_component_clause,[],[f643])).
% 1.63/0.57  fof(f646,plain,(
% 1.63/0.57    ~spl7_6 | spl7_2 | ~spl7_73 | ~spl7_3 | ~spl7_72),
% 1.63/0.57    inference(avatar_split_clause,[],[f640,f633,f103,f643,f96,f115])).
% 1.63/0.57  fof(f633,plain,(
% 1.63/0.57    spl7_72 <=> ! [X2] : (r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 1.63/0.57  fof(f640,plain,(
% 1.63/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | r1_lattice3(sK0,sK2,sK3) | ~l1_orders_2(sK0) | ~spl7_72),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f637])).
% 1.63/0.57  fof(f637,plain,(
% 1.63/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl7_72),
% 1.63/0.57    inference(resolution,[],[f634,f81])).
% 1.63/0.57  fof(f81,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f48])).
% 1.63/0.57  fof(f634,plain,(
% 1.63/0.57    ( ! [X2] : (r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2)) ) | ~spl7_72),
% 1.63/0.57    inference(avatar_component_clause,[],[f633])).
% 1.63/0.57  fof(f635,plain,(
% 1.63/0.57    ~spl7_26 | spl7_72 | ~spl7_6 | ~spl7_24 | ~spl7_29),
% 1.63/0.57    inference(avatar_split_clause,[],[f631,f284,f241,f115,f633,f274])).
% 1.63/0.57  fof(f284,plain,(
% 1.63/0.57    spl7_29 <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.63/0.57  fof(f631,plain,(
% 1.63/0.57    ( ! [X2] : (r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_24 | ~spl7_29)),
% 1.63/0.57    inference(forward_demodulation,[],[f629,f285])).
% 1.63/0.57  fof(f285,plain,(
% 1.63/0.57    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_29),
% 1.63/0.57    inference(avatar_component_clause,[],[f284])).
% 1.63/0.57  fof(f629,plain,(
% 1.63/0.57    ( ! [X2] : (~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) | r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_24)),
% 1.63/0.57    inference(resolution,[],[f593,f242])).
% 1.63/0.57  fof(f242,plain,(
% 1.63/0.57    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~spl7_24),
% 1.63/0.57    inference(avatar_component_clause,[],[f241])).
% 1.63/0.57  fof(f593,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r1_lattice3(sK0,sK4(X1),X0) | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f581,f58])).
% 1.63/0.57  fof(f58,plain,(
% 1.63/0.57    ( ! [X5] : (r2_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f581,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~r2_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1) | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f127,f116])).
% 1.63/0.57  fof(f127,plain,(
% 1.63/0.57    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))) )),
% 1.63/0.57    inference(subsumption_resolution,[],[f90,f84])).
% 1.63/0.57  fof(f90,plain,(
% 1.63/0.57    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(equality_resolution,[],[f74])).
% 1.63/0.57  fof(f74,plain,(
% 1.63/0.57    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f44])).
% 1.63/0.57  fof(f421,plain,(
% 1.63/0.57    ~spl7_6 | spl7_45 | ~spl7_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f417,f115,f419,f115])).
% 1.63/0.57  fof(f417,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 1.63/0.57    inference(duplicate_literal_removal,[],[f416])).
% 1.63/0.57  fof(f416,plain,(
% 1.63/0.57    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f415,f81])).
% 1.63/0.57  fof(f323,plain,(
% 1.63/0.57    ~spl7_9 | spl7_23),
% 1.63/0.57    inference(avatar_split_clause,[],[f235,f232,f155])).
% 1.63/0.57  fof(f155,plain,(
% 1.63/0.57    spl7_9 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.63/0.57  fof(f232,plain,(
% 1.63/0.57    spl7_23 <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.63/0.57  fof(f235,plain,(
% 1.63/0.57    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_23),
% 1.63/0.57    inference(resolution,[],[f233,f86])).
% 1.63/0.57  fof(f233,plain,(
% 1.63/0.57    ~r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | spl7_23),
% 1.63/0.57    inference(avatar_component_clause,[],[f232])).
% 1.63/0.57  fof(f292,plain,(
% 1.63/0.57    ~spl7_4 | ~spl7_24 | spl7_26),
% 1.63/0.57    inference(avatar_split_clause,[],[f291,f274,f241,f107])).
% 1.63/0.57  fof(f107,plain,(
% 1.63/0.57    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.63/0.57  fof(f291,plain,(
% 1.63/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_24 | spl7_26)),
% 1.63/0.57    inference(resolution,[],[f272,f275])).
% 1.63/0.57  fof(f275,plain,(
% 1.63/0.57    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_26),
% 1.63/0.57    inference(avatar_component_clause,[],[f274])).
% 1.63/0.57  fof(f272,plain,(
% 1.63/0.57    ( ! [X0] : (m1_subset_1(sK6(sK0,sK2,sK3),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | ~spl7_24),
% 1.63/0.57    inference(resolution,[],[f242,f89])).
% 1.63/0.57  fof(f89,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f30])).
% 1.63/0.57  fof(f30,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.63/0.57    inference(flattening,[],[f29])).
% 1.63/0.57  fof(f29,plain,(
% 1.63/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.63/0.57    inference(ennf_transformation,[],[f5])).
% 1.63/0.57  fof(f5,axiom,(
% 1.63/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.63/0.57  fof(f286,plain,(
% 1.63/0.57    ~spl7_26 | spl7_29 | ~spl7_24),
% 1.63/0.57    inference(avatar_split_clause,[],[f271,f241,f284,f274])).
% 1.63/0.57  fof(f271,plain,(
% 1.63/0.57    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_24),
% 1.63/0.57    inference(resolution,[],[f242,f59])).
% 1.63/0.57  fof(f59,plain,(
% 1.63/0.57    ( ! [X5] : (~r2_hidden(X5,sK2) | k2_yellow_0(sK0,sK4(X5)) = X5 | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f254,plain,(
% 1.63/0.57    ~spl7_6 | spl7_20),
% 1.63/0.57    inference(avatar_split_clause,[],[f252,f216,f115])).
% 1.63/0.57  fof(f252,plain,(
% 1.63/0.57    ~l1_orders_2(sK0) | spl7_20),
% 1.63/0.57    inference(resolution,[],[f217,f84])).
% 1.63/0.57  fof(f217,plain,(
% 1.63/0.57    ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | spl7_20),
% 1.63/0.57    inference(avatar_component_clause,[],[f216])).
% 1.63/0.57  fof(f243,plain,(
% 1.63/0.57    spl7_24 | ~spl7_3 | spl7_2 | ~spl7_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f239,f115,f96,f103,f241])).
% 1.63/0.57  fof(f239,plain,(
% 1.63/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK2,sK3),sK2) | (spl7_2 | ~spl7_6)),
% 1.63/0.57    inference(resolution,[],[f97,f152])).
% 1.63/0.57  fof(f152,plain,(
% 1.63/0.57    ( ! [X0,X1] : (r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0)) ) | ~spl7_6),
% 1.63/0.57    inference(resolution,[],[f80,f116])).
% 1.63/0.57  fof(f80,plain,(
% 1.63/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f48])).
% 1.63/0.57  fof(f97,plain,(
% 1.63/0.57    ~r1_lattice3(sK0,sK2,sK3) | spl7_2),
% 1.63/0.57    inference(avatar_component_clause,[],[f96])).
% 1.63/0.57  fof(f234,plain,(
% 1.63/0.57    ~spl7_23 | spl7_22),
% 1.63/0.57    inference(avatar_split_clause,[],[f230,f225,f232])).
% 1.63/0.57  fof(f230,plain,(
% 1.63/0.57    ~r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | spl7_22),
% 1.63/0.57    inference(resolution,[],[f226,f88])).
% 1.63/0.57  fof(f88,plain,(
% 1.63/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f50])).
% 1.63/0.57  fof(f226,plain,(
% 1.63/0.57    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl7_22),
% 1.63/0.57    inference(avatar_component_clause,[],[f225])).
% 1.63/0.57  fof(f229,plain,(
% 1.63/0.57    spl7_21),
% 1.63/0.57    inference(avatar_contradiction_clause,[],[f228])).
% 1.63/0.57  fof(f228,plain,(
% 1.63/0.57    $false | spl7_21),
% 1.63/0.57    inference(resolution,[],[f223,f66])).
% 1.63/0.57  fof(f66,plain,(
% 1.63/0.57    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f6])).
% 1.63/0.57  fof(f6,axiom,(
% 1.63/0.57    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).
% 1.63/0.57  fof(f223,plain,(
% 1.63/0.57    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_21),
% 1.63/0.57    inference(avatar_component_clause,[],[f222])).
% 1.63/0.57  fof(f227,plain,(
% 1.63/0.57    ~spl7_21 | ~spl7_22 | spl7_10 | spl7_17),
% 1.63/0.57    inference(avatar_split_clause,[],[f220,f203,f162,f225,f222])).
% 1.63/0.57  fof(f220,plain,(
% 1.63/0.57    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_17),
% 1.63/0.57    inference(resolution,[],[f218,f60])).
% 1.63/0.57  fof(f60,plain,(
% 1.63/0.57    ( ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f218,plain,(
% 1.63/0.57    ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl7_17),
% 1.63/0.57    inference(avatar_component_clause,[],[f203])).
% 1.63/0.57  fof(f177,plain,(
% 1.63/0.57    ~spl7_8 | ~spl7_10),
% 1.63/0.57    inference(avatar_split_clause,[],[f168,f162,f123])).
% 1.63/0.57  fof(f123,plain,(
% 1.63/0.57    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 1.63/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.63/0.57  fof(f168,plain,(
% 1.63/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl7_10),
% 1.63/0.57    inference(superposition,[],[f65,f163])).
% 1.63/0.57  fof(f163,plain,(
% 1.63/0.57    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_10),
% 1.63/0.57    inference(avatar_component_clause,[],[f162])).
% 1.63/0.57  fof(f65,plain,(
% 1.63/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.63/0.57    inference(cnf_transformation,[],[f2])).
% 1.63/0.57  fof(f2,axiom,(
% 1.63/0.57    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.63/0.57  fof(f158,plain,(
% 1.63/0.57    spl7_9 | ~spl7_3 | spl7_1 | ~spl7_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f153,f115,f93,f103,f155])).
% 1.63/0.57  fof(f153,plain,(
% 1.63/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK1,sK3),sK1) | (spl7_1 | ~spl7_6)),
% 1.63/0.57    inference(resolution,[],[f152,f94])).
% 1.63/0.57  fof(f94,plain,(
% 1.63/0.57    ~r1_lattice3(sK0,sK1,sK3) | spl7_1),
% 1.63/0.57    inference(avatar_component_clause,[],[f93])).
% 1.63/0.57  fof(f125,plain,(
% 1.63/0.57    spl7_8),
% 1.63/0.57    inference(avatar_split_clause,[],[f64,f123])).
% 1.63/0.57  fof(f64,plain,(
% 1.63/0.57    v1_xboole_0(k1_xboole_0)),
% 1.63/0.57    inference(cnf_transformation,[],[f1])).
% 1.63/0.57  fof(f1,axiom,(
% 1.63/0.57    v1_xboole_0(k1_xboole_0)),
% 1.63/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.63/0.57  fof(f121,plain,(
% 1.63/0.57    spl7_7),
% 1.63/0.57    inference(avatar_split_clause,[],[f51,f119])).
% 1.63/0.57  fof(f51,plain,(
% 1.63/0.57    v4_orders_2(sK0)),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f117,plain,(
% 1.63/0.57    spl7_6),
% 1.63/0.57    inference(avatar_split_clause,[],[f52,f115])).
% 1.63/0.57  fof(f52,plain,(
% 1.63/0.57    l1_orders_2(sK0)),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f109,plain,(
% 1.63/0.57    spl7_4),
% 1.63/0.57    inference(avatar_split_clause,[],[f54,f107])).
% 1.63/0.57  fof(f54,plain,(
% 1.63/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f105,plain,(
% 1.63/0.57    spl7_3),
% 1.63/0.57    inference(avatar_split_clause,[],[f61,f103])).
% 1.63/0.57  fof(f61,plain,(
% 1.63/0.57    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f101,plain,(
% 1.63/0.57    spl7_1 | spl7_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f62,f96,f93])).
% 1.63/0.57  fof(f62,plain,(
% 1.63/0.57    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  fof(f98,plain,(
% 1.63/0.57    ~spl7_1 | ~spl7_2),
% 1.63/0.57    inference(avatar_split_clause,[],[f63,f96,f93])).
% 1.63/0.57  fof(f63,plain,(
% 1.63/0.57    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 1.63/0.57    inference(cnf_transformation,[],[f39])).
% 1.63/0.57  % SZS output end Proof for theBenchmark
% 1.63/0.57  % (22192)------------------------------
% 1.63/0.57  % (22192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (22192)Termination reason: Refutation
% 1.63/0.57  
% 1.63/0.57  % (22192)Memory used [KB]: 11513
% 1.63/0.57  % (22192)Time elapsed: 0.127 s
% 1.63/0.57  % (22192)------------------------------
% 1.63/0.57  % (22192)------------------------------
% 1.63/0.57  % (22185)Success in time 0.221 s
%------------------------------------------------------------------------------
