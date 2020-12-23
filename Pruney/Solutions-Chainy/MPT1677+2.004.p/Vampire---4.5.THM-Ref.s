%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:18 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 720 expanded)
%              Number of leaves         :   55 ( 317 expanded)
%              Depth                    :   17
%              Number of atoms          : 1335 (7597 expanded)
%              Number of equality atoms :   73 ( 751 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2766,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f102,f106,f110,f114,f118,f122,f126,f130,f134,f167,f172,f187,f231,f233,f236,f261,f283,f339,f370,f373,f679,f693,f740,f821,f1399,f1963,f1982,f2005,f2013,f2016,f2023,f2057,f2090,f2138,f2738,f2764,f2765])).

fof(f2765,plain,
    ( ~ spl7_23
    | spl7_169
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f2666,f738,f217,f116,f104,f97,f1246,f213])).

fof(f213,plain,
    ( spl7_23
  <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1246,plain,
    ( spl7_169
  <=> r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f97,plain,
    ( spl7_2
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f104,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f116,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f217,plain,
    ( spl7_24
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f738,plain,
    ( spl7_102
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f2666,plain,
    ( r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_102 ),
    inference(resolution,[],[f2092,f218])).

fof(f218,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f2092,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | r3_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f101,f1203])).

fof(f1203,plain,
    ( ! [X6,X5] :
        ( ~ r1_lattice3(sK0,X6,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK3,X5)
        | ~ r2_hidden(X5,X6) )
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f888,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f888,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,X2)
        | ~ r2_hidden(X3,X4) )
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(duplicate_literal_removal,[],[f885])).

fof(f885,plain,
    ( ! [X4,X2,X3] :
        ( r3_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,X4) )
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f739,f650])).

fof(f650,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f79,f117])).

fof(f117,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f739,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f738])).

fof(f101,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f2764,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_16
    | spl7_354 ),
    inference(avatar_split_clause,[],[f2763,f2736,f180,f229,f226])).

fof(f226,plain,
    ( spl7_25
  <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f229,plain,
    ( spl7_26
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f180,plain,
    ( spl7_16
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f2736,plain,
    ( spl7_354
  <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_354])])).

fof(f2763,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_354 ),
    inference(resolution,[],[f2737,f58])).

fof(f58,plain,(
    ! [X7] :
      ( r2_yellow_0(sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X7) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f40,f39,f38,f37,f36])).

fof(f36,plain,
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
        & v4_orders_2(X0)
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
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,(
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

fof(f35,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f2737,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_354 ),
    inference(avatar_component_clause,[],[f2736])).

fof(f2738,plain,
    ( ~ spl7_354
    | ~ spl7_23
    | spl7_274
    | ~ spl7_6
    | ~ spl7_183 ),
    inference(avatar_split_clause,[],[f2729,f1397,f116,f2136,f213,f2736])).

fof(f2136,plain,
    ( spl7_274
  <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).

fof(f1397,plain,
    ( spl7_183
  <=> ! [X1] :
        ( ~ r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f2729,plain,
    ( r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_6
    | ~ spl7_183 ),
    inference(resolution,[],[f1398,f298])).

fof(f298,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f92,f117])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1398,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X1,sK3) )
    | ~ spl7_183 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f2138,plain,
    ( ~ spl7_274
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_6
    | spl7_268 ),
    inference(avatar_split_clause,[],[f2128,f2088,f116,f185,f104,f2136])).

fof(f185,plain,
    ( spl7_17
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f2088,plain,
    ( spl7_268
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f2128,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_6
    | spl7_268 ),
    inference(resolution,[],[f2089,f332])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X0),X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f70,f117])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f2089,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))
    | spl7_268 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f2090,plain,
    ( ~ spl7_17
    | ~ spl7_268
    | ~ spl7_3
    | spl7_1
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f2083,f337,f116,f94,f104,f2088,f185])).

fof(f94,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f337,plain,
    ( spl7_37
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f2083,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(resolution,[],[f95,f405])).

fof(f405,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK6(sK0,X0,X1))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(resolution,[],[f380,f338])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f337])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f71,f117])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f2057,plain,
    ( ~ spl7_40
    | ~ spl7_14
    | spl7_258
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_102
    | ~ spl7_257 ),
    inference(avatar_split_clause,[],[f2049,f2011,f738,f116,f112,f104,f94,f2021,f170,f358])).

fof(f358,plain,
    ( spl7_40
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f170,plain,
    ( spl7_14
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f2021,plain,
    ( spl7_258
  <=> r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f112,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f2011,plain,
    ( spl7_257
  <=> r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_257])])).

fof(f2049,plain,
    ( r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))
    | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_102
    | ~ spl7_257 ),
    inference(resolution,[],[f2012,f1373])).

fof(f1373,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK4(X3))
        | r3_orders_2(sK0,sK3,X2)
        | ~ r2_hidden(X3,sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f1343,f60])).

fof(f60,plain,(
    ! [X5] :
      ( m1_subset_1(sK4(X5),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1343,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,X1)
        | r3_orders_2(sK0,sK3,X0) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1237,f1340])).

fof(f1340,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X4,X5)
        | m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl7_5 ),
    inference(resolution,[],[f147,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f147,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | m1_subset_1(X4,X3)
      | ~ r2_hidden(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f90,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f1237,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | r3_orders_2(sK0,sK3,X0) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f1220,f86])).

fof(f1220,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r3_orders_2(sK0,sK3,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_102 ),
    inference(resolution,[],[f1203,f100])).

fof(f100,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f2012,plain,
    ( r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_257 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2023,plain,
    ( ~ spl7_254
    | ~ spl7_3
    | ~ spl7_258
    | ~ spl7_92
    | spl7_255 ),
    inference(avatar_split_clause,[],[f2017,f2003,f677,f2021,f104,f2000])).

fof(f2000,plain,
    ( spl7_254
  <=> m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f677,plain,
    ( spl7_92
  <=> ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f2003,plain,
    ( spl7_255
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_255])])).

fof(f2017,plain,
    ( ~ r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0))
    | ~ spl7_92
    | spl7_255 ),
    inference(resolution,[],[f2004,f678])).

fof(f678,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f677])).

fof(f2004,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))
    | spl7_255 ),
    inference(avatar_component_clause,[],[f2003])).

fof(f2016,plain,
    ( ~ spl7_6
    | ~ spl7_3
    | spl7_250
    | spl7_254 ),
    inference(avatar_split_clause,[],[f2014,f2000,f1980,f104,f116])).

fof(f1980,plain,
    ( spl7_250
  <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_250])])).

fof(f2014,plain,
    ( r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_254 ),
    inference(resolution,[],[f2001,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2001,plain,
    ( ~ m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0))
    | spl7_254 ),
    inference(avatar_component_clause,[],[f2000])).

fof(f2013,plain,
    ( spl7_257
    | ~ spl7_3
    | ~ spl7_6
    | spl7_250 ),
    inference(avatar_split_clause,[],[f1998,f1980,f116,f104,f2011])).

fof(f1998,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_6
    | spl7_250 ),
    inference(resolution,[],[f1981,f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0,X1),X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f81,f117])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1981,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_250 ),
    inference(avatar_component_clause,[],[f1980])).

fof(f2005,plain,
    ( ~ spl7_254
    | ~ spl7_255
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_37
    | spl7_250 ),
    inference(avatar_split_clause,[],[f1996,f1980,f337,f116,f104,f2003,f2000])).

fof(f1996,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))
    | ~ m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_37
    | spl7_250 ),
    inference(resolution,[],[f1981,f405])).

fof(f1982,plain,
    ( ~ spl7_250
    | ~ spl7_3
    | spl7_94
    | ~ spl7_248 ),
    inference(avatar_split_clause,[],[f1971,f1961,f691,f104,f1980])).

fof(f691,plain,
    ( spl7_94
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f1961,plain,
    ( spl7_248
  <=> ! [X5] :
        ( r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).

fof(f1971,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_94
    | ~ spl7_248 ),
    inference(resolution,[],[f1962,f692])).

fof(f692,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | spl7_94 ),
    inference(avatar_component_clause,[],[f691])).

fof(f1962,plain,
    ( ! [X5] :
        ( r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) )
    | ~ spl7_248 ),
    inference(avatar_component_clause,[],[f1961])).

fof(f1963,plain,
    ( ~ spl7_40
    | spl7_248
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1959,f368,f170,f116,f1961,f358])).

fof(f368,plain,
    ( spl7_43
  <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f1959,plain,
    ( ! [X5] :
        ( r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f1958,f369])).

fof(f369,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f368])).

fof(f1958,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5)
        | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(duplicate_literal_removal,[],[f1957])).

fof(f1957,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5)
        | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f1955,f369])).

fof(f1955,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0))
        | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f1322,f171])).

fof(f171,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f1322,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r1_lattice3(sK0,sK4(X1),X0)
        | ~ m1_subset_1(k2_yellow_0(sK0,sK4(X1)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f1185,f61])).

fof(f61,plain,(
    ! [X5] :
      ( r2_yellow_0(sK0,sK4(X5))
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1185,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f91,f117])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1399,plain,
    ( spl7_183
    | ~ spl7_23
    | ~ spl7_3
    | ~ spl7_92
    | ~ spl7_117
    | ~ spl7_169 ),
    inference(avatar_split_clause,[],[f1392,f1246,f819,f677,f104,f213,f1397])).

fof(f819,plain,
    ( spl7_117
  <=> ! [X1,X0,X2] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f1392,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X1,sK3) )
    | ~ spl7_92
    | ~ spl7_117
    | ~ spl7_169 ),
    inference(resolution,[],[f1194,f1247])).

fof(f1247,plain,
    ( r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_169 ),
    inference(avatar_component_clause,[],[f1246])).

fof(f1194,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X2)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_92
    | ~ spl7_117 ),
    inference(duplicate_literal_removal,[],[f1189])).

fof(f1189,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X2)
        | ~ r3_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_92
    | ~ spl7_117 ),
    inference(resolution,[],[f820,f678])).

fof(f820,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,X1)
        | r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl7_117 ),
    inference(avatar_component_clause,[],[f819])).

fof(f821,plain,
    ( ~ spl7_6
    | spl7_117
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f817,f120,f819,f116])).

fof(f120,plain,
    ( spl7_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f817,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f83,f121])).

fof(f121,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f740,plain,
    ( spl7_9
    | ~ spl7_8
    | spl7_102
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f736,f116,f738,f124,f128])).

fof(f128,plain,
    ( spl7_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f124,plain,
    ( spl7_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f736,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f89,f117])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f693,plain,
    ( ~ spl7_40
    | ~ spl7_94
    | ~ spl7_3
    | spl7_2
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f688,f337,f116,f97,f104,f691,f358])).

fof(f688,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6
    | ~ spl7_37 ),
    inference(resolution,[],[f405,f98])).

fof(f98,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f679,plain,
    ( spl7_9
    | ~ spl7_8
    | spl7_92
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f673,f116,f677,f124,f128])).

fof(f673,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f117])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f373,plain,
    ( ~ spl7_6
    | ~ spl7_3
    | spl7_2
    | spl7_40 ),
    inference(avatar_split_clause,[],[f372,f358,f97,f104,f116])).

fof(f372,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_40 ),
    inference(resolution,[],[f359,f80])).

fof(f359,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_40 ),
    inference(avatar_component_clause,[],[f358])).

fof(f370,plain,
    ( ~ spl7_40
    | spl7_43
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f355,f170,f368,f358])).

fof(f355,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f171,f62])).

fof(f62,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | k2_yellow_0(sK0,sK4(X5)) = X5
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f339,plain,
    ( ~ spl7_6
    | spl7_37
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f334,f116,f337,f116])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f332,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f283,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_16
    | spl7_24 ),
    inference(avatar_split_clause,[],[f281,f217,f180,f229,f226])).

fof(f281,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_24 ),
    inference(resolution,[],[f222,f63])).

fof(f63,plain,(
    ! [X4] :
      ( r2_hidden(k2_yellow_0(sK0,X4),sK2)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f222,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f261,plain,
    ( ~ spl7_10
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f243,f180,f132])).

fof(f132,plain,
    ( spl7_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f243,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_16 ),
    inference(superposition,[],[f68,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f68,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f236,plain,
    ( ~ spl7_13
    | spl7_26 ),
    inference(avatar_split_clause,[],[f234,f229,f164])).

fof(f164,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f234,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_26 ),
    inference(resolution,[],[f230,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f230,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f233,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f227,f69])).

fof(f69,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f227,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f226])).

fof(f231,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_16
    | ~ spl7_4
    | spl7_23 ),
    inference(avatar_split_clause,[],[f224,f213,f108,f180,f229,f226])).

fof(f108,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f224,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | spl7_23 ),
    inference(resolution,[],[f221,f151])).

fof(f151,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v1_finset_1(X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f146,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | m1_subset_1(k2_yellow_0(sK0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X1) ) ),
    inference(resolution,[],[f90,f63])).

fof(f221,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f187,plain,
    ( spl7_17
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f183,f164,f112,f185])).

fof(f183,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(resolution,[],[f175,f113])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,sK1,sK3),X0) )
    | ~ spl7_13 ),
    inference(resolution,[],[f165,f90])).

fof(f165,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( spl7_14
    | ~ spl7_3
    | spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f168,f116,f97,f104,f170])).

fof(f168,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f98,f161])).

fof(f167,plain,
    ( spl7_13
    | ~ spl7_3
    | spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f162,f116,f94,f104,f164])).

fof(f162,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_1
    | ~ spl7_6 ),
    inference(resolution,[],[f161,f95])).

fof(f134,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f67,f132])).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f130,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f52,f128])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f122,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f118,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f56,f112])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f57,f108])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f64,f104])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f65,f97,f94])).

fof(f65,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f97,f94])).

fof(f66,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (2967)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (2959)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (2952)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (2971)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (2961)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (2953)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (2963)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (2957)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (2954)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (2969)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (2960)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (2966)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (2958)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (2970)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (2965)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (2955)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (2968)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (2972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (2956)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (2962)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (2964)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.67/0.72  % (2958)Refutation found. Thanks to Tanya!
% 2.67/0.72  % SZS status Theorem for theBenchmark
% 2.67/0.72  % SZS output start Proof for theBenchmark
% 2.67/0.72  fof(f2766,plain,(
% 2.67/0.72    $false),
% 2.67/0.72    inference(avatar_sat_refutation,[],[f99,f102,f106,f110,f114,f118,f122,f126,f130,f134,f167,f172,f187,f231,f233,f236,f261,f283,f339,f370,f373,f679,f693,f740,f821,f1399,f1963,f1982,f2005,f2013,f2016,f2023,f2057,f2090,f2138,f2738,f2764,f2765])).
% 2.67/0.72  fof(f2765,plain,(
% 2.67/0.72    ~spl7_23 | spl7_169 | ~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_24 | ~spl7_102),
% 2.67/0.72    inference(avatar_split_clause,[],[f2666,f738,f217,f116,f104,f97,f1246,f213])).
% 2.67/0.72  fof(f213,plain,(
% 2.67/0.72    spl7_23 <=> m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.67/0.72  fof(f1246,plain,(
% 2.67/0.72    spl7_169 <=> r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).
% 2.67/0.72  fof(f97,plain,(
% 2.67/0.72    spl7_2 <=> r1_lattice3(sK0,sK2,sK3)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.67/0.72  fof(f104,plain,(
% 2.67/0.72    spl7_3 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.67/0.72  fof(f116,plain,(
% 2.67/0.72    spl7_6 <=> l1_orders_2(sK0)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.67/0.72  fof(f217,plain,(
% 2.67/0.72    spl7_24 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.67/0.72  fof(f738,plain,(
% 2.67/0.72    spl7_102 <=> ! [X1,X0] : (~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 2.67/0.72  fof(f2666,plain,(
% 2.67/0.72    r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | (~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_24 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f2092,f218])).
% 2.67/0.72  fof(f218,plain,(
% 2.67/0.72    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_24),
% 2.67/0.72    inference(avatar_component_clause,[],[f217])).
% 2.67/0.72  fof(f2092,plain,(
% 2.67/0.72    ( ! [X2] : (~r2_hidden(X2,sK2) | r3_orders_2(sK0,sK3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl7_2 | ~spl7_3 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f101,f1203])).
% 2.67/0.72  fof(f1203,plain,(
% 2.67/0.72    ( ! [X6,X5] : (~r1_lattice3(sK0,X6,sK3) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r3_orders_2(sK0,sK3,X5) | ~r2_hidden(X5,X6)) ) | (~spl7_3 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f888,f105])).
% 2.67/0.72  fof(f105,plain,(
% 2.67/0.72    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_3),
% 2.67/0.72    inference(avatar_component_clause,[],[f104])).
% 2.67/0.72  fof(f888,plain,(
% 2.67/0.72    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r3_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X4,X2) | ~r2_hidden(X3,X4)) ) | (~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(duplicate_literal_removal,[],[f885])).
% 2.67/0.72  fof(f885,plain,(
% 2.67/0.72    ( ! [X4,X2,X3] : (r3_orders_2(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,X4)) ) | (~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f739,f650])).
% 2.67/0.72  fof(f650,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f79,f117])).
% 2.67/0.72  fof(f117,plain,(
% 2.67/0.72    l1_orders_2(sK0) | ~spl7_6),
% 2.67/0.72    inference(avatar_component_clause,[],[f116])).
% 2.67/0.72  fof(f79,plain,(
% 2.67/0.72    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f50])).
% 2.67/0.72  fof(f50,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 2.67/0.72  fof(f49,plain,(
% 2.67/0.72    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f48,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(rectify,[],[f47])).
% 2.67/0.72  fof(f47,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(nnf_transformation,[],[f22])).
% 2.67/0.72  fof(f22,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(flattening,[],[f21])).
% 2.67/0.72  fof(f21,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(ennf_transformation,[],[f9])).
% 2.67/0.72  fof(f9,axiom,(
% 2.67/0.72    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 2.67/0.72  fof(f739,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_102),
% 2.67/0.72    inference(avatar_component_clause,[],[f738])).
% 2.67/0.72  fof(f101,plain,(
% 2.67/0.72    r1_lattice3(sK0,sK2,sK3) | ~spl7_2),
% 2.67/0.72    inference(avatar_component_clause,[],[f97])).
% 2.67/0.72  fof(f2764,plain,(
% 2.67/0.72    ~spl7_25 | ~spl7_26 | spl7_16 | spl7_354),
% 2.67/0.72    inference(avatar_split_clause,[],[f2763,f2736,f180,f229,f226])).
% 2.67/0.72  fof(f226,plain,(
% 2.67/0.72    spl7_25 <=> v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.67/0.72  fof(f229,plain,(
% 2.67/0.72    spl7_26 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.67/0.72  fof(f180,plain,(
% 2.67/0.72    spl7_16 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.67/0.72  fof(f2736,plain,(
% 2.67/0.72    spl7_354 <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_354])])).
% 2.67/0.72  fof(f2763,plain,(
% 2.67/0.72    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_354),
% 2.67/0.72    inference(resolution,[],[f2737,f58])).
% 2.67/0.72  fof(f58,plain,(
% 2.67/0.72    ( ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f41])).
% 2.67/0.72  fof(f41,plain,(
% 2.67/0.72    ((((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : ((k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 2.67/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f35,f40,f39,f38,f37,f36])).
% 2.67/0.72  fof(f36,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f37,plain,(
% 2.67/0.72    ? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,X1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f38,plain,(
% 2.67/0.72    ? [X2] : (? [X3] : ((~r1_lattice3(sK0,X2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,X2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) & ! [X7] : (r2_yellow_0(sK0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(sK1)) | ~v1_finset_1(X7)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f39,plain,(
% 2.67/0.72    ? [X3] : ((~r1_lattice3(sK0,sK2,X3) | ~r1_lattice3(sK0,sK1,X3)) & (r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)) & (r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f40,plain,(
% 2.67/0.72    ! [X5] : (? [X6] : (k2_yellow_0(sK0,X6) = X5 & r2_yellow_0(sK0,X6) & m1_subset_1(X6,k1_zfmisc_1(sK1)) & v1_finset_1(X6)) => (k2_yellow_0(sK0,sK4(X5)) = X5 & r2_yellow_0(sK0,sK4(X5)) & m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) & v1_finset_1(sK4(X5))))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f35,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattice3(X0,X2,X3) | ~r1_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & ! [X4] : (r2_hidden(k2_yellow_0(X0,X4),X2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~v1_finset_1(X4)) & ! [X5] : (? [X6] : (k2_yellow_0(X0,X6) = X5 & r2_yellow_0(X0,X6) & m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,u1_struct_0(X0))) & ! [X7] : (r2_yellow_0(X0,X7) | k1_xboole_0 = X7 | ~m1_subset_1(X7,k1_zfmisc_1(X1)) | ~v1_finset_1(X7)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.67/0.72    inference(rectify,[],[f34])).
% 2.67/0.72  fof(f34,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.67/0.72    inference(flattening,[],[f33])).
% 2.67/0.72  fof(f33,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X7] : (((~r1_lattice3(X0,X2,X7) | ~r1_lattice3(X0,X1,X7)) & (r1_lattice3(X0,X2,X7) | r1_lattice3(X0,X1,X7))) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.67/0.72    inference(nnf_transformation,[],[f17])).
% 2.67/0.72  fof(f17,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.67/0.72    inference(flattening,[],[f16])).
% 2.67/0.72  fof(f16,plain,(
% 2.67/0.72    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.67/0.72    inference(ennf_transformation,[],[f15])).
% 2.67/0.72  fof(f15,plain,(
% 2.67/0.72    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 2.67/0.72    inference(rectify,[],[f14])).
% 2.67/0.72  fof(f14,negated_conjecture,(
% 2.67/0.72    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 2.67/0.72    inference(negated_conjecture,[],[f13])).
% 2.67/0.72  fof(f13,conjecture,(
% 2.67/0.72    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).
% 2.67/0.72  fof(f2737,plain,(
% 2.67/0.72    ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl7_354),
% 2.67/0.72    inference(avatar_component_clause,[],[f2736])).
% 2.67/0.72  fof(f2738,plain,(
% 2.67/0.72    ~spl7_354 | ~spl7_23 | spl7_274 | ~spl7_6 | ~spl7_183),
% 2.67/0.72    inference(avatar_split_clause,[],[f2729,f1397,f116,f2136,f213,f2736])).
% 2.67/0.72  fof(f2136,plain,(
% 2.67/0.72    spl7_274 <=> r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).
% 2.67/0.72  fof(f1397,plain,(
% 2.67/0.72    spl7_183 <=> ! [X1] : (~r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X1,sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).
% 2.67/0.72  fof(f2729,plain,(
% 2.67/0.72    r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_6 | ~spl7_183)),
% 2.67/0.72    inference(resolution,[],[f1398,f298])).
% 2.67/0.72  fof(f298,plain,(
% 2.67/0.72    ( ! [X0] : (r1_lattice3(sK0,X0,k2_yellow_0(sK0,X0)) | ~m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,X0)) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f92,f117])).
% 2.67/0.72  fof(f92,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))) )),
% 2.67/0.72    inference(equality_resolution,[],[f74])).
% 2.67/0.72  fof(f74,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f46])).
% 2.67/0.72  fof(f46,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.67/0.72  fof(f45,plain,(
% 2.67/0.72    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 2.67/0.72    introduced(choice_axiom,[])).
% 2.67/0.72  fof(f44,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(rectify,[],[f43])).
% 2.67/0.72  fof(f43,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(flattening,[],[f42])).
% 2.67/0.72  fof(f42,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(nnf_transformation,[],[f20])).
% 2.67/0.72  fof(f20,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(flattening,[],[f19])).
% 2.67/0.72  fof(f19,plain,(
% 2.67/0.72    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(ennf_transformation,[],[f10])).
% 2.67/0.72  fof(f10,axiom,(
% 2.67/0.72    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 2.67/0.72  fof(f1398,plain,(
% 2.67/0.72    ( ! [X1] : (~r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X1,sK3)) ) | ~spl7_183),
% 2.67/0.72    inference(avatar_component_clause,[],[f1397])).
% 2.67/0.72  fof(f2138,plain,(
% 2.67/0.72    ~spl7_274 | ~spl7_3 | ~spl7_17 | ~spl7_6 | spl7_268),
% 2.67/0.72    inference(avatar_split_clause,[],[f2128,f2088,f116,f185,f104,f2136])).
% 2.67/0.72  fof(f185,plain,(
% 2.67/0.72    spl7_17 <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.67/0.72  fof(f2088,plain,(
% 2.67/0.72    spl7_268 <=> r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).
% 2.67/0.72  fof(f2128,plain,(
% 2.67/0.72    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | (~spl7_6 | spl7_268)),
% 2.67/0.72    inference(resolution,[],[f2089,f332])).
% 2.67/0.72  fof(f332,plain,(
% 2.67/0.72    ( ! [X0,X1] : (r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(X0),X1)) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f70,f117])).
% 2.67/0.72  fof(f70,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f18])).
% 2.67/0.72  fof(f18,plain,(
% 2.67/0.72    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.67/0.72    inference(ennf_transformation,[],[f12])).
% 2.67/0.72  fof(f12,axiom,(
% 2.67/0.72    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 2.67/0.72  fof(f2089,plain,(
% 2.67/0.72    ~r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3)) | spl7_268),
% 2.67/0.72    inference(avatar_component_clause,[],[f2088])).
% 2.67/0.72  fof(f2090,plain,(
% 2.67/0.72    ~spl7_17 | ~spl7_268 | ~spl7_3 | spl7_1 | ~spl7_6 | ~spl7_37),
% 2.67/0.72    inference(avatar_split_clause,[],[f2083,f337,f116,f94,f104,f2088,f185])).
% 2.67/0.72  fof(f94,plain,(
% 2.67/0.72    spl7_1 <=> r1_lattice3(sK0,sK1,sK3)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.67/0.72  fof(f337,plain,(
% 2.67/0.72    spl7_37 <=> ! [X1,X0] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 2.67/0.72  fof(f2083,plain,(
% 2.67/0.72    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3)) | ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl7_1 | ~spl7_6 | ~spl7_37)),
% 2.67/0.72    inference(resolution,[],[f95,f405])).
% 2.67/0.72  fof(f405,plain,(
% 2.67/0.72    ( ! [X0,X1] : (r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK6(sK0,X0,X1)) | ~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_37)),
% 2.67/0.72    inference(duplicate_literal_removal,[],[f404])).
% 2.67/0.72  fof(f404,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK6(sK0,X0,X1)) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_37)),
% 2.67/0.72    inference(resolution,[],[f380,f338])).
% 2.67/0.72  fof(f338,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_37),
% 2.67/0.72    inference(avatar_component_clause,[],[f337])).
% 2.67/0.72  fof(f380,plain,(
% 2.67/0.72    ( ! [X0,X1] : (r1_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f71,f117])).
% 2.67/0.72  fof(f71,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(X0,k1_tarski(X2),X1)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f18])).
% 2.67/0.72  fof(f95,plain,(
% 2.67/0.72    ~r1_lattice3(sK0,sK1,sK3) | spl7_1),
% 2.67/0.72    inference(avatar_component_clause,[],[f94])).
% 2.67/0.72  fof(f2057,plain,(
% 2.67/0.72    ~spl7_40 | ~spl7_14 | spl7_258 | ~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_102 | ~spl7_257),
% 2.67/0.72    inference(avatar_split_clause,[],[f2049,f2011,f738,f116,f112,f104,f94,f2021,f170,f358])).
% 2.67/0.72  fof(f358,plain,(
% 2.67/0.72    spl7_40 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 2.67/0.72  fof(f170,plain,(
% 2.67/0.72    spl7_14 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.67/0.72  fof(f2021,plain,(
% 2.67/0.72    spl7_258 <=> r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).
% 2.67/0.72  fof(f112,plain,(
% 2.67/0.72    spl7_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.67/0.72  fof(f2011,plain,(
% 2.67/0.72    spl7_257 <=> r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_257])])).
% 2.67/0.72  fof(f2049,plain,(
% 2.67/0.72    r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_102 | ~spl7_257)),
% 2.67/0.72    inference(resolution,[],[f2012,f1373])).
% 2.67/0.72  fof(f1373,plain,(
% 2.67/0.72    ( ! [X2,X3] : (~r2_hidden(X2,sK4(X3)) | r3_orders_2(sK0,sK3,X2) | ~r2_hidden(X3,sK2) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f1343,f60])).
% 2.67/0.72  fof(f60,plain,(
% 2.67/0.72    ( ! [X5] : (m1_subset_1(sK4(X5),k1_zfmisc_1(sK1)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 2.67/0.72    inference(cnf_transformation,[],[f41])).
% 2.67/0.72  fof(f1343,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,X1) | r3_orders_2(sK0,sK3,X0)) ) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(subsumption_resolution,[],[f1237,f1340])).
% 2.67/0.72  fof(f1340,plain,(
% 2.67/0.72    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(sK1)) | ~r2_hidden(X4,X5) | m1_subset_1(X4,u1_struct_0(sK0))) ) | ~spl7_5),
% 2.67/0.72    inference(resolution,[],[f147,f113])).
% 2.67/0.72  fof(f113,plain,(
% 2.67/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 2.67/0.72    inference(avatar_component_clause,[],[f112])).
% 2.67/0.72  fof(f147,plain,(
% 2.67/0.72    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | m1_subset_1(X4,X3) | ~r2_hidden(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X2))) )),
% 2.67/0.72    inference(resolution,[],[f90,f86])).
% 2.67/0.72  fof(f86,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.67/0.72    inference(cnf_transformation,[],[f26])).
% 2.67/0.72  fof(f26,plain,(
% 2.67/0.72    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.67/0.72    inference(ennf_transformation,[],[f3])).
% 2.67/0.72  fof(f3,axiom,(
% 2.67/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.67/0.72  fof(f90,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f32])).
% 2.67/0.72  fof(f32,plain,(
% 2.67/0.72    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.67/0.72    inference(flattening,[],[f31])).
% 2.67/0.72  fof(f31,plain,(
% 2.67/0.72    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.67/0.72    inference(ennf_transformation,[],[f5])).
% 2.67/0.72  fof(f5,axiom,(
% 2.67/0.72    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.67/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.67/0.72  fof(f1237,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r3_orders_2(sK0,sK3,X0)) ) | (~spl7_1 | ~spl7_3 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f1220,f86])).
% 2.67/0.72  fof(f1220,plain,(
% 2.67/0.72    ( ! [X8] : (~r2_hidden(X8,sK1) | r3_orders_2(sK0,sK3,X8) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (~spl7_1 | ~spl7_3 | ~spl7_6 | ~spl7_102)),
% 2.67/0.72    inference(resolution,[],[f1203,f100])).
% 2.67/0.72  fof(f100,plain,(
% 2.67/0.72    r1_lattice3(sK0,sK1,sK3) | ~spl7_1),
% 2.67/0.72    inference(avatar_component_clause,[],[f94])).
% 2.67/0.72  fof(f2012,plain,(
% 2.67/0.72    r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3))) | ~spl7_257),
% 2.67/0.72    inference(avatar_component_clause,[],[f2011])).
% 2.67/0.72  fof(f2023,plain,(
% 2.67/0.72    ~spl7_254 | ~spl7_3 | ~spl7_258 | ~spl7_92 | spl7_255),
% 2.67/0.72    inference(avatar_split_clause,[],[f2017,f2003,f677,f2021,f104,f2000])).
% 2.67/0.72  fof(f2000,plain,(
% 2.67/0.72    spl7_254 <=> m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).
% 2.67/0.72  fof(f677,plain,(
% 2.67/0.72    spl7_92 <=> ! [X1,X0] : (~r3_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 2.67/0.72  fof(f2003,plain,(
% 2.67/0.72    spl7_255 <=> r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_255])])).
% 2.67/0.72  fof(f2017,plain,(
% 2.67/0.72    ~r3_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0)) | (~spl7_92 | spl7_255)),
% 2.67/0.72    inference(resolution,[],[f2004,f678])).
% 2.67/0.72  fof(f678,plain,(
% 2.67/0.72    ( ! [X0,X1] : (r1_orders_2(sK0,X0,X1) | ~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_92),
% 2.67/0.72    inference(avatar_component_clause,[],[f677])).
% 2.67/0.72  fof(f2004,plain,(
% 2.67/0.72    ~r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) | spl7_255),
% 2.67/0.72    inference(avatar_component_clause,[],[f2003])).
% 2.67/0.72  fof(f2016,plain,(
% 2.67/0.72    ~spl7_6 | ~spl7_3 | spl7_250 | spl7_254),
% 2.67/0.72    inference(avatar_split_clause,[],[f2014,f2000,f1980,f104,f116])).
% 2.67/0.72  fof(f1980,plain,(
% 2.67/0.72    spl7_250 <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_250])])).
% 2.67/0.72  fof(f2014,plain,(
% 2.67/0.72    r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl7_254),
% 2.67/0.72    inference(resolution,[],[f2001,f80])).
% 2.67/0.72  fof(f80,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f50])).
% 2.67/0.72  fof(f2001,plain,(
% 2.67/0.72    ~m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0)) | spl7_254),
% 2.67/0.72    inference(avatar_component_clause,[],[f2000])).
% 2.67/0.72  fof(f2013,plain,(
% 2.67/0.72    spl7_257 | ~spl7_3 | ~spl7_6 | spl7_250),
% 2.67/0.72    inference(avatar_split_clause,[],[f1998,f1980,f116,f104,f2011])).
% 2.67/0.72  fof(f1998,plain,(
% 2.67/0.72    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),sK4(sK6(sK0,sK2,sK3))) | (~spl7_6 | spl7_250)),
% 2.67/0.72    inference(resolution,[],[f1981,f161])).
% 2.67/0.72  fof(f161,plain,(
% 2.67/0.72    ( ! [X0,X1] : (r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0)) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f81,f117])).
% 2.67/0.72  fof(f81,plain,(
% 2.67/0.72    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 2.67/0.72    inference(cnf_transformation,[],[f50])).
% 2.67/0.72  fof(f1981,plain,(
% 2.67/0.72    ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_250),
% 2.67/0.72    inference(avatar_component_clause,[],[f1980])).
% 2.67/0.72  fof(f2005,plain,(
% 2.67/0.72    ~spl7_254 | ~spl7_255 | ~spl7_3 | ~spl7_6 | ~spl7_37 | spl7_250),
% 2.67/0.72    inference(avatar_split_clause,[],[f1996,f1980,f337,f116,f104,f2003,f2000])).
% 2.67/0.72  fof(f1996,plain,(
% 2.67/0.72    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK3,sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)) | ~m1_subset_1(sK6(sK0,sK4(sK6(sK0,sK2,sK3)),sK3),u1_struct_0(sK0)) | (~spl7_6 | ~spl7_37 | spl7_250)),
% 2.67/0.72    inference(resolution,[],[f1981,f405])).
% 2.67/0.72  fof(f1982,plain,(
% 2.67/0.72    ~spl7_250 | ~spl7_3 | spl7_94 | ~spl7_248),
% 2.67/0.72    inference(avatar_split_clause,[],[f1971,f1961,f691,f104,f1980])).
% 2.67/0.72  fof(f691,plain,(
% 2.67/0.72    spl7_94 <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).
% 2.67/0.72  fof(f1961,plain,(
% 2.67/0.72    spl7_248 <=> ! [X5] : (r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).
% 2.67/0.72  fof(f1971,plain,(
% 2.67/0.72    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (spl7_94 | ~spl7_248)),
% 2.67/0.72    inference(resolution,[],[f1962,f692])).
% 2.67/0.72  fof(f692,plain,(
% 2.67/0.72    ~r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | spl7_94),
% 2.67/0.72    inference(avatar_component_clause,[],[f691])).
% 2.67/0.72  fof(f1962,plain,(
% 2.67/0.72    ( ! [X5] : (r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5)) ) | ~spl7_248),
% 2.67/0.72    inference(avatar_component_clause,[],[f1961])).
% 2.67/0.72  fof(f1963,plain,(
% 2.67/0.72    ~spl7_40 | spl7_248 | ~spl7_6 | ~spl7_14 | ~spl7_43),
% 2.67/0.72    inference(avatar_split_clause,[],[f1959,f368,f170,f116,f1961,f358])).
% 2.67/0.72  fof(f368,plain,(
% 2.67/0.72    spl7_43 <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 2.67/0.72    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.67/0.72  fof(f1959,plain,(
% 2.67/0.72    ( ! [X5] : (r1_orders_2(sK0,X5,sK6(sK0,sK2,sK3)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_14 | ~spl7_43)),
% 2.67/0.72    inference(forward_demodulation,[],[f1958,f369])).
% 2.67/0.72  fof(f369,plain,(
% 2.67/0.72    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_43),
% 2.67/0.72    inference(avatar_component_clause,[],[f368])).
% 2.67/0.72  fof(f1958,plain,(
% 2.67/0.72    ( ! [X5] : (~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_14 | ~spl7_43)),
% 2.67/0.72    inference(duplicate_literal_removal,[],[f1957])).
% 2.67/0.72  fof(f1957,plain,(
% 2.67/0.72    ( ! [X5] : (~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_14 | ~spl7_43)),
% 2.67/0.72    inference(forward_demodulation,[],[f1955,f369])).
% 2.67/0.72  fof(f1955,plain,(
% 2.67/0.72    ( ! [X5] : (~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X5) | ~m1_subset_1(k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))),u1_struct_0(sK0)) | r1_orders_2(sK0,X5,k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl7_6 | ~spl7_14)),
% 2.67/0.72    inference(resolution,[],[f1322,f171])).
% 2.67/0.72  fof(f171,plain,(
% 2.67/0.72    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~spl7_14),
% 2.67/0.72    inference(avatar_component_clause,[],[f170])).
% 2.67/0.72  fof(f1322,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~r2_hidden(X1,sK2) | ~r1_lattice3(sK0,sK4(X1),X0) | ~m1_subset_1(k2_yellow_0(sK0,sK4(X1)),u1_struct_0(sK0)) | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK4(X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f1185,f61])).
% 2.67/0.72  fof(f61,plain,(
% 2.67/0.72    ( ! [X5] : (r2_yellow_0(sK0,sK4(X5)) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 2.67/0.72    inference(cnf_transformation,[],[f41])).
% 2.67/0.72  fof(f1185,plain,(
% 2.67/0.72    ( ! [X0,X1] : (~r2_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))) ) | ~spl7_6),
% 2.67/0.72    inference(resolution,[],[f91,f117])).
% 3.02/0.74  fof(f91,plain,(
% 3.02/0.74    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))) )),
% 3.02/0.74    inference(equality_resolution,[],[f75])).
% 3.02/0.74  fof(f75,plain,(
% 3.02/0.74    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f46])).
% 3.02/0.74  fof(f1399,plain,(
% 3.02/0.74    spl7_183 | ~spl7_23 | ~spl7_3 | ~spl7_92 | ~spl7_117 | ~spl7_169),
% 3.02/0.74    inference(avatar_split_clause,[],[f1392,f1246,f819,f677,f104,f213,f1397])).
% 3.02/0.74  fof(f819,plain,(
% 3.02/0.74    spl7_117 <=> ! [X1,X0,X2] : (~r1_lattice3(sK0,X0,X1) | r1_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X1))),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).
% 3.02/0.74  fof(f1392,plain,(
% 3.02/0.74    ( ! [X1] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X1,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X1,sK3)) ) | (~spl7_92 | ~spl7_117 | ~spl7_169)),
% 3.02/0.74    inference(resolution,[],[f1194,f1247])).
% 3.02/0.74  fof(f1247,plain,(
% 3.02/0.74    r3_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~spl7_169),
% 3.02/0.74    inference(avatar_component_clause,[],[f1246])).
% 3.02/0.74  fof(f1194,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~r3_orders_2(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X2) | r1_lattice3(sK0,X0,X1)) ) | (~spl7_92 | ~spl7_117)),
% 3.02/0.74    inference(duplicate_literal_removal,[],[f1189])).
% 3.02/0.74  fof(f1189,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X2) | ~r3_orders_2(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl7_92 | ~spl7_117)),
% 3.02/0.74    inference(resolution,[],[f820,f678])).
% 3.02/0.74  fof(f820,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X2,X1) | r1_lattice3(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1)) ) | ~spl7_117),
% 3.02/0.74    inference(avatar_component_clause,[],[f819])).
% 3.02/0.74  fof(f821,plain,(
% 3.02/0.74    ~spl7_6 | spl7_117 | ~spl7_7),
% 3.02/0.74    inference(avatar_split_clause,[],[f817,f120,f819,f116])).
% 3.02/0.74  fof(f120,plain,(
% 3.02/0.74    spl7_7 <=> v4_orders_2(sK0)),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 3.02/0.74  fof(f817,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~r1_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,X0,X2)) ) | ~spl7_7),
% 3.02/0.74    inference(resolution,[],[f83,f121])).
% 3.02/0.74  fof(f121,plain,(
% 3.02/0.74    v4_orders_2(sK0) | ~spl7_7),
% 3.02/0.74    inference(avatar_component_clause,[],[f120])).
% 3.02/0.74  fof(f83,plain,(
% 3.02/0.74    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X3,X1)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f24])).
% 3.02/0.74  fof(f24,plain,(
% 3.02/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 3.02/0.74    inference(flattening,[],[f23])).
% 3.02/0.74  fof(f23,plain,(
% 3.02/0.74    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 3.02/0.74    inference(ennf_transformation,[],[f11])).
% 3.02/0.74  fof(f11,axiom,(
% 3.02/0.74    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).
% 3.02/0.74  fof(f740,plain,(
% 3.02/0.74    spl7_9 | ~spl7_8 | spl7_102 | ~spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f736,f116,f738,f124,f128])).
% 3.02/0.74  fof(f128,plain,(
% 3.02/0.74    spl7_9 <=> v2_struct_0(sK0)),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 3.02/0.74  fof(f124,plain,(
% 3.02/0.74    spl7_8 <=> v3_orders_2(sK0)),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 3.02/0.74  fof(f736,plain,(
% 3.02/0.74    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 3.02/0.74    inference(resolution,[],[f89,f117])).
% 3.02/0.74  fof(f89,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f51])).
% 3.02/0.74  fof(f51,plain,(
% 3.02/0.74    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.02/0.74    inference(nnf_transformation,[],[f30])).
% 3.02/0.74  fof(f30,plain,(
% 3.02/0.74    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 3.02/0.74    inference(flattening,[],[f29])).
% 3.02/0.74  fof(f29,plain,(
% 3.02/0.74    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 3.02/0.74    inference(ennf_transformation,[],[f7])).
% 3.02/0.74  fof(f7,axiom,(
% 3.02/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 3.02/0.74  fof(f693,plain,(
% 3.02/0.74    ~spl7_40 | ~spl7_94 | ~spl7_3 | spl7_2 | ~spl7_6 | ~spl7_37),
% 3.02/0.74    inference(avatar_split_clause,[],[f688,f337,f116,f97,f104,f691,f358])).
% 3.02/0.74  fof(f688,plain,(
% 3.02/0.74    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (spl7_2 | ~spl7_6 | ~spl7_37)),
% 3.02/0.74    inference(resolution,[],[f405,f98])).
% 3.02/0.74  fof(f98,plain,(
% 3.02/0.74    ~r1_lattice3(sK0,sK2,sK3) | spl7_2),
% 3.02/0.74    inference(avatar_component_clause,[],[f97])).
% 3.02/0.74  fof(f679,plain,(
% 3.02/0.74    spl7_9 | ~spl7_8 | spl7_92 | ~spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f673,f116,f677,f124,f128])).
% 3.02/0.74  fof(f673,plain,(
% 3.02/0.74    ( ! [X0,X1] : (~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 3.02/0.74    inference(resolution,[],[f88,f117])).
% 3.02/0.74  fof(f88,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f51])).
% 3.02/0.74  fof(f373,plain,(
% 3.02/0.74    ~spl7_6 | ~spl7_3 | spl7_2 | spl7_40),
% 3.02/0.74    inference(avatar_split_clause,[],[f372,f358,f97,f104,f116])).
% 3.02/0.74  fof(f372,plain,(
% 3.02/0.74    r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl7_40),
% 3.02/0.74    inference(resolution,[],[f359,f80])).
% 3.02/0.74  fof(f359,plain,(
% 3.02/0.74    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_40),
% 3.02/0.74    inference(avatar_component_clause,[],[f358])).
% 3.02/0.74  fof(f370,plain,(
% 3.02/0.74    ~spl7_40 | spl7_43 | ~spl7_14),
% 3.02/0.74    inference(avatar_split_clause,[],[f355,f170,f368,f358])).
% 3.02/0.74  fof(f355,plain,(
% 3.02/0.74    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_14),
% 3.02/0.74    inference(resolution,[],[f171,f62])).
% 3.02/0.74  fof(f62,plain,(
% 3.02/0.74    ( ! [X5] : (~r2_hidden(X5,sK2) | k2_yellow_0(sK0,sK4(X5)) = X5 | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f339,plain,(
% 3.02/0.74    ~spl7_6 | spl7_37 | ~spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f334,f116,f337,f116])).
% 3.02/0.74  fof(f334,plain,(
% 3.02/0.74    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 3.02/0.74    inference(duplicate_literal_removal,[],[f333])).
% 3.02/0.74  fof(f333,plain,(
% 3.02/0.74    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl7_6),
% 3.02/0.74    inference(resolution,[],[f332,f82])).
% 3.02/0.74  fof(f82,plain,(
% 3.02/0.74    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f50])).
% 3.02/0.74  fof(f283,plain,(
% 3.02/0.74    ~spl7_25 | ~spl7_26 | spl7_16 | spl7_24),
% 3.02/0.74    inference(avatar_split_clause,[],[f281,f217,f180,f229,f226])).
% 3.02/0.74  fof(f281,plain,(
% 3.02/0.74    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_24),
% 3.02/0.74    inference(resolution,[],[f222,f63])).
% 3.02/0.74  fof(f63,plain,(
% 3.02/0.74    ( ! [X4] : (r2_hidden(k2_yellow_0(sK0,X4),sK2) | k1_xboole_0 = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~v1_finset_1(X4)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f222,plain,(
% 3.02/0.74    ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl7_24),
% 3.02/0.74    inference(avatar_component_clause,[],[f217])).
% 3.02/0.74  fof(f261,plain,(
% 3.02/0.74    ~spl7_10 | ~spl7_16),
% 3.02/0.74    inference(avatar_split_clause,[],[f243,f180,f132])).
% 3.02/0.74  fof(f132,plain,(
% 3.02/0.74    spl7_10 <=> v1_xboole_0(k1_xboole_0)),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.02/0.74  fof(f243,plain,(
% 3.02/0.74    ~v1_xboole_0(k1_xboole_0) | ~spl7_16),
% 3.02/0.74    inference(superposition,[],[f68,f181])).
% 3.02/0.74  fof(f181,plain,(
% 3.02/0.74    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_16),
% 3.02/0.74    inference(avatar_component_clause,[],[f180])).
% 3.02/0.74  fof(f68,plain,(
% 3.02/0.74    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.02/0.74    inference(cnf_transformation,[],[f2])).
% 3.02/0.74  fof(f2,axiom,(
% 3.02/0.74    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 3.02/0.74  fof(f236,plain,(
% 3.02/0.74    ~spl7_13 | spl7_26),
% 3.02/0.74    inference(avatar_split_clause,[],[f234,f229,f164])).
% 3.02/0.74  fof(f164,plain,(
% 3.02/0.74    spl7_13 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 3.02/0.74  fof(f234,plain,(
% 3.02/0.74    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_26),
% 3.02/0.74    inference(resolution,[],[f230,f85])).
% 3.02/0.74  fof(f85,plain,(
% 3.02/0.74    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.74    inference(cnf_transformation,[],[f25])).
% 3.02/0.74  fof(f25,plain,(
% 3.02/0.74    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.02/0.74    inference(ennf_transformation,[],[f4])).
% 3.02/0.74  fof(f4,axiom,(
% 3.02/0.74    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 3.02/0.74  fof(f230,plain,(
% 3.02/0.74    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl7_26),
% 3.02/0.74    inference(avatar_component_clause,[],[f229])).
% 3.02/0.74  fof(f233,plain,(
% 3.02/0.74    spl7_25),
% 3.02/0.74    inference(avatar_contradiction_clause,[],[f232])).
% 3.02/0.74  fof(f232,plain,(
% 3.02/0.74    $false | spl7_25),
% 3.02/0.74    inference(resolution,[],[f227,f69])).
% 3.02/0.74  fof(f69,plain,(
% 3.02/0.74    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 3.02/0.74    inference(cnf_transformation,[],[f6])).
% 3.02/0.74  fof(f6,axiom,(
% 3.02/0.74    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 3.02/0.74  fof(f227,plain,(
% 3.02/0.74    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_25),
% 3.02/0.74    inference(avatar_component_clause,[],[f226])).
% 3.02/0.74  fof(f231,plain,(
% 3.02/0.74    ~spl7_25 | ~spl7_26 | spl7_16 | ~spl7_4 | spl7_23),
% 3.02/0.74    inference(avatar_split_clause,[],[f224,f213,f108,f180,f229,f226])).
% 3.02/0.74  fof(f108,plain,(
% 3.02/0.74    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.02/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 3.02/0.74  fof(f224,plain,(
% 3.02/0.74    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_4 | spl7_23)),
% 3.02/0.74    inference(resolution,[],[f221,f151])).
% 3.02/0.74  fof(f151,plain,(
% 3.02/0.74    ( ! [X0] : (m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v1_finset_1(X0)) ) | ~spl7_4),
% 3.02/0.74    inference(resolution,[],[f146,f109])).
% 3.02/0.74  fof(f109,plain,(
% 3.02/0.74    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_4),
% 3.02/0.74    inference(avatar_component_clause,[],[f108])).
% 3.02/0.74  fof(f146,plain,(
% 3.02/0.74    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | m1_subset_1(k2_yellow_0(sK0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~v1_finset_1(X1)) )),
% 3.02/0.74    inference(resolution,[],[f90,f63])).
% 3.02/0.74  fof(f221,plain,(
% 3.02/0.74    ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | spl7_23),
% 3.02/0.74    inference(avatar_component_clause,[],[f213])).
% 3.02/0.74  fof(f187,plain,(
% 3.02/0.74    spl7_17 | ~spl7_5 | ~spl7_13),
% 3.02/0.74    inference(avatar_split_clause,[],[f183,f164,f112,f185])).
% 3.02/0.74  fof(f183,plain,(
% 3.02/0.74    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | (~spl7_5 | ~spl7_13)),
% 3.02/0.74    inference(resolution,[],[f175,f113])).
% 3.02/0.74  fof(f175,plain,(
% 3.02/0.74    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK0,sK1,sK3),X0)) ) | ~spl7_13),
% 3.02/0.74    inference(resolution,[],[f165,f90])).
% 3.02/0.74  fof(f165,plain,(
% 3.02/0.74    r2_hidden(sK6(sK0,sK1,sK3),sK1) | ~spl7_13),
% 3.02/0.74    inference(avatar_component_clause,[],[f164])).
% 3.02/0.74  fof(f172,plain,(
% 3.02/0.74    spl7_14 | ~spl7_3 | spl7_2 | ~spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f168,f116,f97,f104,f170])).
% 3.02/0.74  fof(f168,plain,(
% 3.02/0.74    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK2,sK3),sK2) | (spl7_2 | ~spl7_6)),
% 3.02/0.74    inference(resolution,[],[f98,f161])).
% 3.02/0.74  fof(f167,plain,(
% 3.02/0.74    spl7_13 | ~spl7_3 | spl7_1 | ~spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f162,f116,f94,f104,f164])).
% 3.02/0.74  fof(f162,plain,(
% 3.02/0.74    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK1,sK3),sK1) | (spl7_1 | ~spl7_6)),
% 3.02/0.74    inference(resolution,[],[f161,f95])).
% 3.02/0.74  fof(f134,plain,(
% 3.02/0.74    spl7_10),
% 3.02/0.74    inference(avatar_split_clause,[],[f67,f132])).
% 3.02/0.74  fof(f67,plain,(
% 3.02/0.74    v1_xboole_0(k1_xboole_0)),
% 3.02/0.74    inference(cnf_transformation,[],[f1])).
% 3.02/0.74  fof(f1,axiom,(
% 3.02/0.74    v1_xboole_0(k1_xboole_0)),
% 3.02/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.02/0.74  fof(f130,plain,(
% 3.02/0.74    ~spl7_9),
% 3.02/0.74    inference(avatar_split_clause,[],[f52,f128])).
% 3.02/0.74  fof(f52,plain,(
% 3.02/0.74    ~v2_struct_0(sK0)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f126,plain,(
% 3.02/0.74    spl7_8),
% 3.02/0.74    inference(avatar_split_clause,[],[f53,f124])).
% 3.02/0.74  fof(f53,plain,(
% 3.02/0.74    v3_orders_2(sK0)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f122,plain,(
% 3.02/0.74    spl7_7),
% 3.02/0.74    inference(avatar_split_clause,[],[f54,f120])).
% 3.02/0.74  fof(f54,plain,(
% 3.02/0.74    v4_orders_2(sK0)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f118,plain,(
% 3.02/0.74    spl7_6),
% 3.02/0.74    inference(avatar_split_clause,[],[f55,f116])).
% 3.02/0.74  fof(f55,plain,(
% 3.02/0.74    l1_orders_2(sK0)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f114,plain,(
% 3.02/0.74    spl7_5),
% 3.02/0.74    inference(avatar_split_clause,[],[f56,f112])).
% 3.02/0.74  fof(f56,plain,(
% 3.02/0.74    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f110,plain,(
% 3.02/0.74    spl7_4),
% 3.02/0.74    inference(avatar_split_clause,[],[f57,f108])).
% 3.02/0.74  fof(f57,plain,(
% 3.02/0.74    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f106,plain,(
% 3.02/0.74    spl7_3),
% 3.02/0.74    inference(avatar_split_clause,[],[f64,f104])).
% 3.02/0.74  fof(f64,plain,(
% 3.02/0.74    m1_subset_1(sK3,u1_struct_0(sK0))),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f102,plain,(
% 3.02/0.74    spl7_1 | spl7_2),
% 3.02/0.74    inference(avatar_split_clause,[],[f65,f97,f94])).
% 3.02/0.74  fof(f65,plain,(
% 3.02/0.74    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  fof(f99,plain,(
% 3.02/0.74    ~spl7_1 | ~spl7_2),
% 3.02/0.74    inference(avatar_split_clause,[],[f66,f97,f94])).
% 3.02/0.74  fof(f66,plain,(
% 3.02/0.74    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 3.02/0.74    inference(cnf_transformation,[],[f41])).
% 3.02/0.74  % SZS output end Proof for theBenchmark
% 3.02/0.74  % (2958)------------------------------
% 3.02/0.74  % (2958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.74  % (2958)Termination reason: Refutation
% 3.02/0.74  
% 3.02/0.74  % (2958)Memory used [KB]: 12792
% 3.02/0.74  % (2958)Time elapsed: 0.303 s
% 3.02/0.74  % (2958)------------------------------
% 3.02/0.74  % (2958)------------------------------
% 3.02/0.74  % (2951)Success in time 0.388 s
%------------------------------------------------------------------------------
