%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 425 expanded)
%              Number of leaves         :   41 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  855 (3411 expanded)
%              Number of equality atoms :  143 ( 594 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f153,f156,f158,f160,f170,f172,f174,f202,f208,f235,f241,f243,f249,f255,f286,f304,f309,f311])).

fof(f311,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f299,f101])).

fof(f101,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
        | ( X6 != X8
          & X5 != X8
          & X4 != X8
          & X3 != X8
          & X2 != X8
          & X1 != X8
          & X0 != X8 ) )
      & ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8
        | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X8,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X6 = X8
        | X5 = X8
        | X4 = X8
        | X3 = X8
        | X2 = X8
        | X1 = X8
        | X0 = X8 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f299,plain,
    ( ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl7_25
  <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f309,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f306,f51])).

fof(f51,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ! [X4] :
          ( sK5 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
      | ! [X5] :
          ( sK5 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
    & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    & ~ r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f37,f36,f35,f34])).

fof(f34,plain,
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
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2))) )
          & ~ r1_tsep_1(sK3,X2)
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2))) )
        & ~ r1_tsep_1(sK3,X2)
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) )
      & ~ r1_tsep_1(sK3,sK4)
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) )
   => ( ( ! [X4] :
            ( sK5 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
        | ! [X5] :
            ( sK5 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
      & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f306,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_26 ),
    inference(resolution,[],[f305,f55])).

fof(f55,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_26 ),
    inference(resolution,[],[f303,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f303,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl7_26
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f304,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f293,f284,f124,f114,f150,f146,f301,f297])).

fof(f146,plain,
    ( spl7_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f150,plain,
    ( spl7_10
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f114,plain,
    ( spl7_2
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f124,plain,
    ( spl7_4
  <=> ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f284,plain,
    ( spl7_24
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f293,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f288,f116])).

fof(f116,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f288,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) )
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f287,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK5,u1_struct_0(X0)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f287,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f285,f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(definition_folding,[],[f30,f32,f31])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

fof(f285,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ m1_pre_topc(X0,sK2)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f284])).

fof(f286,plain,
    ( ~ spl7_6
    | ~ spl7_19
    | spl7_24
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f282,f205,f284,f238,f134])).

fof(f134,plain,
    ( spl7_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f238,plain,
    ( spl7_19
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f205,plain,
    ( spl7_14
  <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f282,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
        | ~ l1_pre_topc(sK2)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7)
        | ~ sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f281,f50])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f281,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7,X8)
        | ~ sP1(X8,X7,X6,X5,X4,X3,X2,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f264,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X8,X7) )
          & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X8,X7) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ~ sP0(X9,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ~ sP0(X8,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(X0),k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f212,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f212,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2)
        | ~ r2_hidden(X2,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f68,f207])).

fof(f207,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f205])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f255,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f251,f51])).

fof(f251,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_20 ),
    inference(resolution,[],[f250,f53])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_20 ),
    inference(resolution,[],[f248,f59])).

fof(f248,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl7_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f249,plain,
    ( spl7_1
    | ~ spl7_20
    | spl7_7
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f244,f232,f124,f138,f246,f110])).

fof(f110,plain,
    ( spl7_1
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f138,plain,
    ( spl7_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f232,plain,
    ( spl7_18
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f244,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f234,f125])).

fof(f234,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f243,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | spl7_19 ),
    inference(avatar_split_clause,[],[f242,f238,f150,f146,f142,f138,f134,f130])).

fof(f130,plain,
    ( spl7_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f142,plain,
    ( spl7_8
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_19 ),
    inference(resolution,[],[f240,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f240,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f238])).

fof(f241,plain,
    ( ~ spl7_19
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f236,f229,f142,f134,f238])).

fof(f229,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl7_17 ),
    inference(resolution,[],[f230,f50])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f235,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f227,f205,f232,f229])).

fof(f227,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f211,f63])).

fof(f211,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3))
    | ~ spl7_14 ),
    inference(superposition,[],[f97,f207])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f65,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f208,plain,
    ( spl7_14
    | spl7_3
    | ~ spl7_8
    | ~ spl7_6
    | spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f203,f200,f130,f134,f142,f120,f205])).

fof(f120,plain,
    ( spl7_3
  <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f200,plain,
    ( spl7_13
  <=> ! [X0] :
        ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK4,X0)
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f203,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_13 ),
    inference(resolution,[],[f201,f55])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl7_7
    | spl7_9
    | spl7_13 ),
    inference(avatar_split_clause,[],[f198,f200,f146,f138])).

fof(f198,plain,(
    ! [X0] :
      ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
      | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f197,f56])).

fof(f56,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(resolution,[],[f195,f72])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(definition_unfolding,[],[f61,f94])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f174,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f148,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f148,plain,
    ( v2_struct_0(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f172,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl7_7 ),
    inference(resolution,[],[f140,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f140,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f170,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f132,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f160,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f152,f55])).

fof(f152,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f158,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f144,f53])).

fof(f144,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f156,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f136,f51])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f153,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f128,f120,f150,f146,f142,f138,f134,f130])).

fof(f128,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f70,f122])).

fof(f122,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f126,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f118,f124,f120])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f117,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f99,f114,f110])).

fof(f99,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X5] :
      ( sK5 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.24/0.53  % (9615)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.53  % (9634)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.53  % (9612)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (9626)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.54  % (9619)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.54  % (9641)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.54  % (9617)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.54  % (9609)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (9621)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.54  % (9630)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.54  % (9625)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.54  % (9614)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.54  % (9613)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.54  % (9611)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.54  % (9635)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.54  % (9620)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (9640)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (9620)Refutation not found, incomplete strategy% (9620)------------------------------
% 1.43/0.55  % (9620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (9620)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (9620)Memory used [KB]: 10746
% 1.43/0.55  % (9620)Time elapsed: 0.133 s
% 1.43/0.55  % (9620)------------------------------
% 1.43/0.55  % (9620)------------------------------
% 1.43/0.55  % (9638)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (9621)Refutation not found, incomplete strategy% (9621)------------------------------
% 1.43/0.55  % (9621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (9610)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.55  % (9636)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (9618)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (9628)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (9633)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (9627)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (9621)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (9621)Memory used [KB]: 10746
% 1.43/0.56  % (9621)Time elapsed: 0.138 s
% 1.43/0.56  % (9621)------------------------------
% 1.43/0.56  % (9621)------------------------------
% 1.43/0.56  % (9632)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (9629)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (9637)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.56  % (9631)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.57  % (9624)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.57  % (9623)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.58  % (9623)Refutation found. Thanks to Tanya!
% 1.43/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f312,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(avatar_sat_refutation,[],[f117,f126,f153,f156,f158,f160,f170,f172,f174,f202,f208,f235,f241,f243,f249,f255,f286,f304,f309,f311])).
% 1.43/0.58  fof(f311,plain,(
% 1.43/0.58    spl7_25),
% 1.43/0.58    inference(avatar_contradiction_clause,[],[f310])).
% 1.43/0.58  fof(f310,plain,(
% 1.43/0.58    $false | spl7_25),
% 1.43/0.58    inference(resolution,[],[f299,f101])).
% 1.43/0.58  fof(f101,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7)) )),
% 1.43/0.58    inference(equality_resolution,[],[f87])).
% 1.43/0.58  fof(f87,plain,(
% 1.43/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | X0 != X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f47])).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 1.43/0.58    inference(rectify,[],[f46])).
% 1.43/0.60  fof(f46,plain,(
% 1.43/0.60    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 1.43/0.60    inference(flattening,[],[f45])).
% 1.43/0.60  fof(f45,plain,(
% 1.43/0.60    ! [X8,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X8,X6,X5,X4,X3,X2,X1,X0) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 1.43/0.60    inference(nnf_transformation,[],[f31])).
% 1.43/0.60  fof(f31,plain,(
% 1.43/0.60    ! [X8,X6,X5,X4,X3,X2,X1,X0] : (sP0(X8,X6,X5,X4,X3,X2,X1,X0) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8))),
% 1.43/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.43/0.60  fof(f299,plain,(
% 1.43/0.60    ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | spl7_25),
% 1.43/0.60    inference(avatar_component_clause,[],[f297])).
% 1.43/0.60  fof(f297,plain,(
% 1.43/0.60    spl7_25 <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.43/0.60  fof(f309,plain,(
% 1.43/0.60    spl7_26),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f307])).
% 1.43/0.60  fof(f307,plain,(
% 1.43/0.60    $false | spl7_26),
% 1.43/0.60    inference(resolution,[],[f306,f51])).
% 1.43/0.60  fof(f51,plain,(
% 1.43/0.60    l1_pre_topc(sK2)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f38,plain,(
% 1.43/0.60    ((((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.43/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f37,f36,f35,f34])).
% 1.43/0.60  fof(f34,plain,(
% 1.43/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f35,plain,(
% 1.43/0.60    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f36,plain,(
% 1.43/0.60    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f37,plain,(
% 1.43/0.60    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) => ((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f19,plain,(
% 1.43/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.60    inference(flattening,[],[f18])).
% 1.43/0.60  fof(f18,plain,(
% 1.43/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f17])).
% 1.43/0.60  fof(f17,plain,(
% 1.43/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.43/0.60    inference(rectify,[],[f16])).
% 1.43/0.60  fof(f16,negated_conjecture,(
% 1.43/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.43/0.60    inference(negated_conjecture,[],[f15])).
% 1.43/0.60  fof(f15,conjecture,(
% 1.43/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.43/0.60  fof(f306,plain,(
% 1.43/0.60    ~l1_pre_topc(sK2) | spl7_26),
% 1.43/0.60    inference(resolution,[],[f305,f55])).
% 1.43/0.60  fof(f55,plain,(
% 1.43/0.60    m1_pre_topc(sK4,sK2)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f305,plain,(
% 1.43/0.60    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) ) | spl7_26),
% 1.43/0.60    inference(resolution,[],[f303,f59])).
% 1.43/0.60  fof(f59,plain,(
% 1.43/0.60    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f20])).
% 1.43/0.60  fof(f20,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.60    inference(ennf_transformation,[],[f10])).
% 1.43/0.60  fof(f10,axiom,(
% 1.43/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.43/0.60  fof(f303,plain,(
% 1.43/0.60    ~l1_pre_topc(sK4) | spl7_26),
% 1.43/0.60    inference(avatar_component_clause,[],[f301])).
% 1.43/0.60  fof(f301,plain,(
% 1.43/0.60    spl7_26 <=> l1_pre_topc(sK4)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.43/0.60  fof(f304,plain,(
% 1.43/0.60    ~spl7_25 | ~spl7_26 | spl7_9 | ~spl7_10 | spl7_2 | ~spl7_4 | ~spl7_24),
% 1.43/0.60    inference(avatar_split_clause,[],[f293,f284,f124,f114,f150,f146,f301,f297])).
% 1.43/0.60  fof(f146,plain,(
% 1.43/0.60    spl7_9 <=> v2_struct_0(sK4)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.43/0.60  fof(f150,plain,(
% 1.43/0.60    spl7_10 <=> m1_pre_topc(sK4,sK2)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.43/0.60  fof(f114,plain,(
% 1.43/0.60    spl7_2 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.43/0.60  fof(f124,plain,(
% 1.43/0.60    spl7_4 <=> ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.43/0.60  fof(f284,plain,(
% 1.43/0.60    spl7_24 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : (~m1_pre_topc(X0,sK2) | ~sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.43/0.60  fof(f293,plain,(
% 1.43/0.60    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | (spl7_2 | ~spl7_4 | ~spl7_24)),
% 1.43/0.60    inference(resolution,[],[f288,f116])).
% 1.43/0.60  fof(f116,plain,(
% 1.43/0.60    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl7_2),
% 1.43/0.60    inference(avatar_component_clause,[],[f114])).
% 1.43/0.60  fof(f288,plain,(
% 1.43/0.60    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))) ) | (~spl7_4 | ~spl7_24)),
% 1.43/0.60    inference(resolution,[],[f287,f125])).
% 1.43/0.60  fof(f125,plain,(
% 1.43/0.60    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK5,u1_struct_0(X0))) ) | ~spl7_4),
% 1.43/0.60    inference(avatar_component_clause,[],[f124])).
% 1.43/0.60  fof(f287,plain,(
% 1.43/0.60    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) ) | ~spl7_24),
% 1.43/0.60    inference(resolution,[],[f285,f108])).
% 1.43/0.60  fof(f108,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.43/0.60    inference(equality_resolution,[],[f88])).
% 1.43/0.60  fof(f88,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 1.43/0.60    inference(cnf_transformation,[],[f48])).
% 1.43/0.60  fof(f48,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 1.43/0.60    inference(nnf_transformation,[],[f33])).
% 1.43/0.60  fof(f33,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7))),
% 1.43/0.60    inference(definition_folding,[],[f30,f32,f31])).
% 1.43/0.60  fof(f32,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> sP0(X8,X6,X5,X4,X3,X2,X1,X0)))),
% 1.43/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.43/0.60  fof(f30,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 1.43/0.60    inference(ennf_transformation,[],[f7])).
% 1.43/0.60  fof(f7,axiom,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).
% 1.43/0.60  fof(f285,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(X0,sK2) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_24),
% 1.43/0.60    inference(avatar_component_clause,[],[f284])).
% 1.43/0.60  fof(f286,plain,(
% 1.43/0.60    ~spl7_6 | ~spl7_19 | spl7_24 | ~spl7_14),
% 1.43/0.60    inference(avatar_split_clause,[],[f282,f205,f284,f238,f134])).
% 1.43/0.60  fof(f134,plain,(
% 1.43/0.60    spl7_6 <=> l1_pre_topc(sK2)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.43/0.60  fof(f238,plain,(
% 1.43/0.60    spl7_19 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.43/0.60  fof(f205,plain,(
% 1.43/0.60    spl7_14 <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.43/0.60  fof(f282,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~l1_pre_topc(sK2) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7) | ~sP1(X7,X6,X5,X4,X3,X2,X1,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 1.43/0.60    inference(resolution,[],[f281,f50])).
% 1.43/0.60  fof(f50,plain,(
% 1.43/0.60    v2_pre_topc(sK2)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f281,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7,X8) | ~sP1(X8,X7,X6,X5,X4,X3,X2,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 1.43/0.60    inference(resolution,[],[f264,f77])).
% 1.43/0.60  fof(f77,plain,(
% 1.43/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f44])).
% 1.43/0.60  fof(f44,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 1.43/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 1.43/0.60  fof(f43,plain,(
% 1.43/0.60    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7))) => ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 1.43/0.60    introduced(choice_axiom,[])).
% 1.43/0.60  fof(f42,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | ~sP0(X9,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 1.43/0.60    inference(rectify,[],[f41])).
% 1.43/0.60  fof(f41,plain,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : ((~sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | ~sP0(X8,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X7))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 1.43/0.60    inference(nnf_transformation,[],[f32])).
% 1.43/0.60  fof(f264,plain,(
% 1.43/0.60    ( ! [X0,X1] : (~r2_hidden(u1_struct_0(X0),k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl7_14),
% 1.43/0.60    inference(resolution,[],[f212,f63])).
% 1.43/0.60  fof(f63,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f40])).
% 1.43/0.60  fof(f40,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.60    inference(nnf_transformation,[],[f26])).
% 1.43/0.60  fof(f26,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.60    inference(flattening,[],[f25])).
% 1.43/0.60  fof(f25,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f14])).
% 1.43/0.60  fof(f14,axiom,(
% 1.43/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.43/0.60  fof(f212,plain,(
% 1.43/0.60    ( ! [X2] : (r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2) | ~r2_hidden(X2,k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 1.43/0.60    inference(superposition,[],[f68,f207])).
% 1.43/0.60  fof(f207,plain,(
% 1.43/0.60    u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_14),
% 1.43/0.60    inference(avatar_component_clause,[],[f205])).
% 1.43/0.60  fof(f68,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f27])).
% 1.43/0.60  fof(f27,plain,(
% 1.43/0.60    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.43/0.60    inference(ennf_transformation,[],[f9])).
% 1.43/0.60  fof(f9,axiom,(
% 1.43/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.43/0.60  fof(f255,plain,(
% 1.43/0.60    spl7_20),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f253])).
% 1.43/0.60  fof(f253,plain,(
% 1.43/0.60    $false | spl7_20),
% 1.43/0.60    inference(resolution,[],[f251,f51])).
% 1.43/0.60  fof(f251,plain,(
% 1.43/0.60    ~l1_pre_topc(sK2) | spl7_20),
% 1.43/0.60    inference(resolution,[],[f250,f53])).
% 1.43/0.60  fof(f53,plain,(
% 1.43/0.60    m1_pre_topc(sK3,sK2)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f250,plain,(
% 1.43/0.60    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl7_20),
% 1.43/0.60    inference(resolution,[],[f248,f59])).
% 1.43/0.60  fof(f248,plain,(
% 1.43/0.60    ~l1_pre_topc(sK3) | spl7_20),
% 1.43/0.60    inference(avatar_component_clause,[],[f246])).
% 1.43/0.60  fof(f246,plain,(
% 1.43/0.60    spl7_20 <=> l1_pre_topc(sK3)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.43/0.60  fof(f249,plain,(
% 1.43/0.60    spl7_1 | ~spl7_20 | spl7_7 | ~spl7_4 | ~spl7_18),
% 1.43/0.60    inference(avatar_split_clause,[],[f244,f232,f124,f138,f246,f110])).
% 1.43/0.60  fof(f110,plain,(
% 1.43/0.60    spl7_1 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.43/0.60  fof(f138,plain,(
% 1.43/0.60    spl7_7 <=> v2_struct_0(sK3)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.43/0.60  fof(f232,plain,(
% 1.43/0.60    spl7_18 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.43/0.60  fof(f244,plain,(
% 1.43/0.60    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_4 | ~spl7_18)),
% 1.43/0.60    inference(resolution,[],[f234,f125])).
% 1.43/0.60  fof(f234,plain,(
% 1.43/0.60    m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~spl7_18),
% 1.43/0.60    inference(avatar_component_clause,[],[f232])).
% 1.43/0.60  fof(f243,plain,(
% 1.43/0.60    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | spl7_19),
% 1.43/0.60    inference(avatar_split_clause,[],[f242,f238,f150,f146,f142,f138,f134,f130])).
% 1.43/0.60  fof(f130,plain,(
% 1.43/0.60    spl7_5 <=> v2_struct_0(sK2)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.43/0.60  fof(f142,plain,(
% 1.43/0.60    spl7_8 <=> m1_pre_topc(sK3,sK2)),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.43/0.60  fof(f242,plain,(
% 1.43/0.60    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | spl7_19),
% 1.43/0.60    inference(resolution,[],[f240,f72])).
% 1.43/0.60  fof(f72,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f29])).
% 1.43/0.60  fof(f29,plain,(
% 1.43/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.60    inference(flattening,[],[f28])).
% 1.43/0.60  fof(f28,plain,(
% 1.43/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f13])).
% 1.43/0.60  fof(f13,axiom,(
% 1.43/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.43/0.60  fof(f240,plain,(
% 1.43/0.60    ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | spl7_19),
% 1.43/0.60    inference(avatar_component_clause,[],[f238])).
% 1.43/0.60  fof(f241,plain,(
% 1.43/0.60    ~spl7_19 | ~spl7_6 | ~spl7_8 | ~spl7_17),
% 1.43/0.60    inference(avatar_split_clause,[],[f236,f229,f142,f134,f238])).
% 1.43/0.60  fof(f229,plain,(
% 1.43/0.60    spl7_17 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.43/0.60  fof(f236,plain,(
% 1.43/0.60    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~spl7_17),
% 1.43/0.60    inference(resolution,[],[f230,f50])).
% 1.43/0.60  fof(f230,plain,(
% 1.43/0.60    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_17),
% 1.43/0.60    inference(avatar_component_clause,[],[f229])).
% 1.43/0.60  fof(f235,plain,(
% 1.43/0.60    spl7_17 | spl7_18 | ~spl7_14),
% 1.43/0.60    inference(avatar_split_clause,[],[f227,f205,f232,f229])).
% 1.43/0.60  fof(f227,plain,(
% 1.43/0.60    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_14),
% 1.43/0.60    inference(resolution,[],[f211,f63])).
% 1.43/0.60  fof(f211,plain,(
% 1.43/0.60    r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) | ~spl7_14),
% 1.43/0.60    inference(superposition,[],[f97,f207])).
% 1.43/0.60  fof(f97,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f65,f94])).
% 1.43/0.60  fof(f94,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.43/0.60    inference(definition_unfolding,[],[f66,f93])).
% 1.43/0.60  fof(f93,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f67,f92])).
% 1.43/0.60  fof(f92,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f69,f91])).
% 1.43/0.60  fof(f91,plain,(
% 1.43/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f73,f90])).
% 1.43/0.60  fof(f90,plain,(
% 1.43/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f74,f75])).
% 1.43/0.60  fof(f75,plain,(
% 1.43/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f6])).
% 1.43/0.60  fof(f6,axiom,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.43/0.60  fof(f74,plain,(
% 1.43/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f5])).
% 1.43/0.60  fof(f5,axiom,(
% 1.43/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.43/0.60  fof(f73,plain,(
% 1.43/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f4])).
% 1.43/0.60  fof(f4,axiom,(
% 1.43/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.43/0.60  fof(f69,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f3])).
% 1.43/0.60  fof(f3,axiom,(
% 1.43/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.60  fof(f67,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f2])).
% 1.43/0.60  fof(f2,axiom,(
% 1.43/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.60  fof(f66,plain,(
% 1.43/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.43/0.60    inference(cnf_transformation,[],[f8])).
% 1.43/0.60  fof(f8,axiom,(
% 1.43/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.60  fof(f65,plain,(
% 1.43/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f1])).
% 1.43/0.60  fof(f1,axiom,(
% 1.43/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.43/0.60  fof(f208,plain,(
% 1.43/0.60    spl7_14 | spl7_3 | ~spl7_8 | ~spl7_6 | spl7_5 | ~spl7_13),
% 1.43/0.60    inference(avatar_split_clause,[],[f203,f200,f130,f134,f142,f120,f205])).
% 1.43/0.60  fof(f120,plain,(
% 1.43/0.60    spl7_3 <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.43/0.60  fof(f200,plain,(
% 1.43/0.60    spl7_13 <=> ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK4,X0) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))))),
% 1.43/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.43/0.60  fof(f203,plain,(
% 1.43/0.60    v2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_13),
% 1.43/0.60    inference(resolution,[],[f201,f55])).
% 1.43/0.60  fof(f201,plain,(
% 1.43/0.60    ( ! [X0] : (~m1_pre_topc(sK4,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_13),
% 1.43/0.60    inference(avatar_component_clause,[],[f200])).
% 1.43/0.60  fof(f202,plain,(
% 1.43/0.60    spl7_7 | spl7_9 | spl7_13),
% 1.43/0.60    inference(avatar_split_clause,[],[f198,f200,f146,f138])).
% 1.43/0.60  fof(f198,plain,(
% 1.43/0.60    ( ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k5_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(resolution,[],[f197,f56])).
% 1.43/0.60  fof(f56,plain,(
% 1.43/0.60    ~r1_tsep_1(sK3,sK4)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f197,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(duplicate_literal_removal,[],[f196])).
% 1.43/0.60  fof(f196,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(resolution,[],[f195,f72])).
% 1.43/0.60  fof(f195,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(duplicate_literal_removal,[],[f194])).
% 1.43/0.60  fof(f194,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(resolution,[],[f100,f71])).
% 1.43/0.60  fof(f71,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f29])).
% 1.43/0.60  fof(f100,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(equality_resolution,[],[f96])).
% 1.43/0.60  fof(f96,plain,(
% 1.43/0.60    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k1_setfam_1(k5_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(definition_unfolding,[],[f61,f94])).
% 1.43/0.60  fof(f61,plain,(
% 1.43/0.60    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f39])).
% 1.43/0.60  fof(f39,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.60    inference(nnf_transformation,[],[f24])).
% 1.43/0.60  fof(f24,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.60    inference(flattening,[],[f23])).
% 1.43/0.60  fof(f23,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f12])).
% 1.43/0.60  fof(f12,axiom,(
% 1.43/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.43/0.60  fof(f174,plain,(
% 1.43/0.60    ~spl7_9),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f173])).
% 1.43/0.60  fof(f173,plain,(
% 1.43/0.60    $false | ~spl7_9),
% 1.43/0.60    inference(resolution,[],[f148,f54])).
% 1.43/0.60  fof(f54,plain,(
% 1.43/0.60    ~v2_struct_0(sK4)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f148,plain,(
% 1.43/0.60    v2_struct_0(sK4) | ~spl7_9),
% 1.43/0.60    inference(avatar_component_clause,[],[f146])).
% 1.43/0.60  fof(f172,plain,(
% 1.43/0.60    ~spl7_7),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f171])).
% 1.43/0.60  fof(f171,plain,(
% 1.43/0.60    $false | ~spl7_7),
% 1.43/0.60    inference(resolution,[],[f140,f52])).
% 1.43/0.60  fof(f52,plain,(
% 1.43/0.60    ~v2_struct_0(sK3)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f140,plain,(
% 1.43/0.60    v2_struct_0(sK3) | ~spl7_7),
% 1.43/0.60    inference(avatar_component_clause,[],[f138])).
% 1.43/0.60  fof(f170,plain,(
% 1.43/0.60    ~spl7_5),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f169])).
% 1.43/0.60  fof(f169,plain,(
% 1.43/0.60    $false | ~spl7_5),
% 1.43/0.60    inference(resolution,[],[f132,f49])).
% 1.43/0.60  fof(f49,plain,(
% 1.43/0.60    ~v2_struct_0(sK2)),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f132,plain,(
% 1.43/0.60    v2_struct_0(sK2) | ~spl7_5),
% 1.43/0.60    inference(avatar_component_clause,[],[f130])).
% 1.43/0.60  fof(f160,plain,(
% 1.43/0.60    spl7_10),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f159])).
% 1.43/0.60  fof(f159,plain,(
% 1.43/0.60    $false | spl7_10),
% 1.43/0.60    inference(resolution,[],[f152,f55])).
% 1.43/0.60  fof(f152,plain,(
% 1.43/0.60    ~m1_pre_topc(sK4,sK2) | spl7_10),
% 1.43/0.60    inference(avatar_component_clause,[],[f150])).
% 1.43/0.60  fof(f158,plain,(
% 1.43/0.60    spl7_8),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f157])).
% 1.43/0.60  fof(f157,plain,(
% 1.43/0.60    $false | spl7_8),
% 1.43/0.60    inference(resolution,[],[f144,f53])).
% 1.43/0.60  fof(f144,plain,(
% 1.43/0.60    ~m1_pre_topc(sK3,sK2) | spl7_8),
% 1.43/0.60    inference(avatar_component_clause,[],[f142])).
% 1.43/0.60  fof(f156,plain,(
% 1.43/0.60    spl7_6),
% 1.43/0.60    inference(avatar_contradiction_clause,[],[f154])).
% 1.43/0.60  fof(f154,plain,(
% 1.43/0.60    $false | spl7_6),
% 1.43/0.60    inference(resolution,[],[f136,f51])).
% 1.43/0.60  fof(f136,plain,(
% 1.43/0.60    ~l1_pre_topc(sK2) | spl7_6),
% 1.43/0.60    inference(avatar_component_clause,[],[f134])).
% 1.43/0.60  fof(f153,plain,(
% 1.43/0.60    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | ~spl7_3),
% 1.43/0.60    inference(avatar_split_clause,[],[f128,f120,f150,f146,f142,f138,f134,f130])).
% 1.43/0.60  fof(f128,plain,(
% 1.43/0.60    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl7_3),
% 1.43/0.60    inference(resolution,[],[f70,f122])).
% 1.43/0.60  fof(f122,plain,(
% 1.43/0.60    v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~spl7_3),
% 1.43/0.60    inference(avatar_component_clause,[],[f120])).
% 1.43/0.60  fof(f70,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f29])).
% 1.43/0.60  fof(f126,plain,(
% 1.43/0.60    spl7_3 | spl7_4),
% 1.43/0.60    inference(avatar_split_clause,[],[f118,f124,f120])).
% 1.43/0.60  fof(f118,plain,(
% 1.43/0.60    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(resolution,[],[f60,f57])).
% 1.43/0.60  fof(f57,plain,(
% 1.43/0.60    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  fof(f60,plain,(
% 1.43/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.60    inference(cnf_transformation,[],[f22])).
% 1.43/0.60  fof(f22,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.60    inference(flattening,[],[f21])).
% 1.43/0.60  fof(f21,plain,(
% 1.43/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.60    inference(ennf_transformation,[],[f11])).
% 1.43/0.60  fof(f11,axiom,(
% 1.43/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.43/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.43/0.60  fof(f117,plain,(
% 1.43/0.60    ~spl7_1 | ~spl7_2),
% 1.43/0.60    inference(avatar_split_clause,[],[f99,f114,f110])).
% 1.43/0.60  fof(f99,plain,(
% 1.43/0.60    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.43/0.60    inference(equality_resolution,[],[f98])).
% 1.43/0.60  fof(f98,plain,(
% 1.43/0.60    ( ! [X5] : (~m1_subset_1(sK5,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 1.43/0.60    inference(equality_resolution,[],[f58])).
% 1.43/0.60  fof(f58,plain,(
% 1.43/0.60    ( ! [X4,X5] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 1.43/0.60    inference(cnf_transformation,[],[f38])).
% 1.43/0.60  % SZS output end Proof for theBenchmark
% 1.43/0.60  % (9623)------------------------------
% 1.43/0.60  % (9623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (9623)Termination reason: Refutation
% 1.43/0.60  
% 1.43/0.60  % (9623)Memory used [KB]: 6524
% 1.43/0.60  % (9623)Time elapsed: 0.175 s
% 1.43/0.60  % (9623)------------------------------
% 1.43/0.60  % (9623)------------------------------
% 1.43/0.61  % (9606)Success in time 0.247 s
%------------------------------------------------------------------------------
