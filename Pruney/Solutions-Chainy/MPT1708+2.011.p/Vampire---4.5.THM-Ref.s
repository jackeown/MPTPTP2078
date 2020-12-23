%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 431 expanded)
%              Number of leaves         :   42 ( 182 expanded)
%              Depth                    :   16
%              Number of atoms          :  867 (3427 expanded)
%              Number of equality atoms :  155 ( 610 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f131,f158,f161,f163,f165,f174,f176,f178,f207,f213,f237,f243,f245,f251,f260,f292,f310,f315,f317])).

fof(f317,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f305,f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f305,plain,
    ( ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl7_25
  <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f315,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f312,f52])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f38,f37,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f312,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_26 ),
    inference(resolution,[],[f311,f56])).

fof(f56,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_26 ),
    inference(resolution,[],[f309,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f309,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl7_26
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f310,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f299,f290,f129,f119,f155,f151,f307,f303])).

fof(f151,plain,
    ( spl7_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f155,plain,
    ( spl7_10
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f119,plain,
    ( spl7_2
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f129,plain,
    ( spl7_4
  <=> ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f290,plain,
    ( spl7_24
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f299,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f297,f121])).

fof(f121,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f297,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) )
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f293,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK5,u1_struct_0(X0)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f293,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f291,f113])).

fof(f113,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f31,f33,f32])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f291,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
        ( ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ m1_pre_topc(X0,sK2)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f290])).

fof(f292,plain,
    ( ~ spl7_6
    | ~ spl7_19
    | spl7_24
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f288,f210,f290,f240,f139])).

fof(f139,plain,
    ( spl7_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f240,plain,
    ( spl7_19
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f210,plain,
    ( spl7_14
  <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f288,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
        | ~ l1_pre_topc(sK2)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8)
        | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f287,f51])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f287,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7,X8,X9)
        | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f270,f79])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(X0),k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f217,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f217,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2)
        | ~ r2_hidden(X2,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f69,f212])).

fof(f212,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f260,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f253,f52])).

fof(f253,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_20 ),
    inference(resolution,[],[f252,f54])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_20 ),
    inference(resolution,[],[f250,f60])).

fof(f250,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f251,plain,
    ( spl7_1
    | ~ spl7_20
    | spl7_7
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f246,f234,f129,f143,f248,f115])).

fof(f115,plain,
    ( spl7_1
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f143,plain,
    ( spl7_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f234,plain,
    ( spl7_18
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f246,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f236,f130])).

fof(f236,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f234])).

fof(f245,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | spl7_19 ),
    inference(avatar_split_clause,[],[f244,f240,f155,f151,f147,f143,f139,f135])).

fof(f135,plain,
    ( spl7_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f147,plain,
    ( spl7_8
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f244,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_19 ),
    inference(resolution,[],[f242,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f242,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f243,plain,
    ( ~ spl7_19
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f238,f231,f147,f139,f240])).

fof(f231,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f238,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl7_17 ),
    inference(resolution,[],[f232,f51])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f231])).

fof(f237,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f229,f210,f234,f231])).

fof(f229,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f216,f64])).

fof(f216,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3))
    | ~ spl7_14 ),
    inference(superposition,[],[f101,f212])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f66,f98])).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f70,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f213,plain,
    ( spl7_14
    | spl7_3
    | ~ spl7_8
    | ~ spl7_6
    | spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f208,f205,f135,f139,f147,f125,f210])).

fof(f125,plain,
    ( spl7_3
  <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f205,plain,
    ( spl7_13
  <=> ! [X0] :
        ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK4,X0)
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f208,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_13 ),
    inference(resolution,[],[f206,f56])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl7_7
    | spl7_9
    | spl7_13 ),
    inference(avatar_split_clause,[],[f203,f205,f151,f143])).

fof(f203,plain,(
    ! [X0] :
      ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
      | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f202,f57])).

fof(f57,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(resolution,[],[f200,f73])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(definition_unfolding,[],[f62,f98])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f178,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f153,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f153,plain,
    ( v2_struct_0(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f176,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl7_7 ),
    inference(resolution,[],[f145,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f174,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f137,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f137,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f165,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f157,f56])).

fof(f157,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f163,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f149,f54])).

fof(f149,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f161,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f141,f52])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f158,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f133,f125,f155,f151,f147,f143,f139,f135])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f71,f127])).

fof(f127,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f131,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f123,f129,f125])).

fof(f123,plain,(
    ! [X0] :
      ( m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f122,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f103,f119,f115])).

fof(f103,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X5] :
      ( sK5 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (20111)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (20103)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (20107)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20102)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (20116)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (20106)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20097)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (20090)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (20096)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (20091)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (20092)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (20104)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (20094)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (20105)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20104)Refutation not found, incomplete strategy% (20104)------------------------------
% 0.22/0.54  % (20104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20104)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20104)Memory used [KB]: 10746
% 0.22/0.54  % (20104)Time elapsed: 0.138 s
% 0.22/0.54  % (20104)------------------------------
% 0.22/0.54  % (20104)------------------------------
% 0.22/0.54  % (20103)Refutation not found, incomplete strategy% (20103)------------------------------
% 0.22/0.54  % (20103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20103)Memory used [KB]: 10746
% 0.22/0.54  % (20103)Time elapsed: 0.136 s
% 0.22/0.54  % (20103)------------------------------
% 0.22/0.54  % (20103)------------------------------
% 0.22/0.54  % (20119)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (20122)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (20114)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (20117)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (20112)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (20109)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (20115)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (20120)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (20123)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (20108)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (20099)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (20113)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (20110)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (20098)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (20101)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (20118)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (20105)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f318,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f122,f131,f158,f161,f163,f165,f174,f176,f178,f207,f213,f237,f243,f245,f251,f260,f292,f310,f315,f317])).
% 0.22/0.56  fof(f317,plain,(
% 0.22/0.56    spl7_25),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f316])).
% 0.22/0.56  fof(f316,plain,(
% 0.22/0.56    $false | spl7_25),
% 0.22/0.56    inference(resolution,[],[f305,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 0.22/0.56    inference(equality_resolution,[],[f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.22/0.56    inference(rectify,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.22/0.56    inference(flattening,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f305,plain,(
% 0.22/0.56    ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | spl7_25),
% 0.22/0.56    inference(avatar_component_clause,[],[f303])).
% 0.22/0.56  fof(f303,plain,(
% 0.22/0.56    spl7_25 <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    spl7_26),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f313])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    $false | spl7_26),
% 0.22/0.56    inference(resolution,[],[f312,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    l1_pre_topc(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ((((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f38,f37,f36,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) => ((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 0.22/0.56    inference(rectify,[],[f17])).
% 0.22/0.56  fof(f17,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f16])).
% 0.22/0.56  fof(f16,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2) | spl7_26),
% 0.22/0.56    inference(resolution,[],[f311,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    m1_pre_topc(sK4,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) ) | spl7_26),
% 0.22/0.56    inference(resolution,[],[f309,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.56  fof(f309,plain,(
% 0.22/0.56    ~l1_pre_topc(sK4) | spl7_26),
% 0.22/0.56    inference(avatar_component_clause,[],[f307])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    spl7_26 <=> l1_pre_topc(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.56  fof(f310,plain,(
% 0.22/0.56    ~spl7_25 | ~spl7_26 | spl7_9 | ~spl7_10 | spl7_2 | ~spl7_4 | ~spl7_24),
% 0.22/0.56    inference(avatar_split_clause,[],[f299,f290,f129,f119,f155,f151,f307,f303])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    spl7_9 <=> v2_struct_0(sK4)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    spl7_10 <=> m1_pre_topc(sK4,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    spl7_2 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    spl7_4 <=> ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.56  fof(f290,plain,(
% 0.22/0.56    spl7_24 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : (~m1_pre_topc(X0,sK2) | ~sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.56  fof(f299,plain,(
% 0.22/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | (spl7_2 | ~spl7_4 | ~spl7_24)),
% 0.22/0.56    inference(resolution,[],[f297,f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl7_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f119])).
% 0.22/0.56  fof(f297,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))) ) | (~spl7_4 | ~spl7_24)),
% 0.22/0.56    inference(resolution,[],[f293,f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK5,u1_struct_0(X0))) ) | ~spl7_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f129])).
% 0.22/0.56  fof(f293,plain,(
% 0.22/0.56    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) ) | ~spl7_24),
% 0.22/0.56    inference(resolution,[],[f291,f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.22/0.56    inference(equality_resolution,[],[f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.22/0.56    inference(cnf_transformation,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.22/0.56    inference(nnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.56    inference(definition_folding,[],[f31,f33,f32])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(X0,sK2) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_24),
% 0.22/0.56    inference(avatar_component_clause,[],[f290])).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    ~spl7_6 | ~spl7_19 | spl7_24 | ~spl7_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f288,f210,f290,f240,f139])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    spl7_6 <=> l1_pre_topc(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    spl7_19 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    spl7_14 <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.56  fof(f288,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~l1_pre_topc(sK2) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6,X7,X8) | ~sP1(X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.22/0.56    inference(resolution,[],[f287,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    v2_pre_topc(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7,X8,X9) | ~sP1(X9,X8,X7,X6,X5,X4,X3,X2,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.22/0.56    inference(resolution,[],[f270,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.22/0.56    inference(rectify,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 0.22/0.56    inference(nnf_transformation,[],[f33])).
% 0.22/0.56  fof(f270,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(u1_struct_0(X0),k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl7_14),
% 0.22/0.56    inference(resolution,[],[f217,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    ( ! [X2] : (r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2) | ~r2_hidden(X2,k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.22/0.56    inference(superposition,[],[f69,f212])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f210])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    spl7_20),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.56  fof(f258,plain,(
% 0.22/0.56    $false | spl7_20),
% 0.22/0.56    inference(resolution,[],[f253,f52])).
% 0.22/0.56  fof(f253,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2) | spl7_20),
% 0.22/0.56    inference(resolution,[],[f252,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    m1_pre_topc(sK3,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f252,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl7_20),
% 0.22/0.56    inference(resolution,[],[f250,f60])).
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    ~l1_pre_topc(sK3) | spl7_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f248])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    spl7_20 <=> l1_pre_topc(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.56  fof(f251,plain,(
% 0.22/0.56    spl7_1 | ~spl7_20 | spl7_7 | ~spl7_4 | ~spl7_18),
% 0.22/0.56    inference(avatar_split_clause,[],[f246,f234,f129,f143,f248,f115])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    spl7_1 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    spl7_7 <=> v2_struct_0(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.56  fof(f234,plain,(
% 0.22/0.56    spl7_18 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.56  fof(f246,plain,(
% 0.22/0.56    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_4 | ~spl7_18)),
% 0.22/0.56    inference(resolution,[],[f236,f130])).
% 0.22/0.56  fof(f236,plain,(
% 0.22/0.56    m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~spl7_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f234])).
% 0.22/0.56  fof(f245,plain,(
% 0.22/0.56    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | spl7_19),
% 0.22/0.56    inference(avatar_split_clause,[],[f244,f240,f155,f151,f147,f143,f139,f135])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    spl7_5 <=> v2_struct_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    spl7_8 <=> m1_pre_topc(sK3,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.56  fof(f244,plain,(
% 0.22/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | spl7_19),
% 0.22/0.56    inference(resolution,[],[f242,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.22/0.56  fof(f242,plain,(
% 0.22/0.56    ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | spl7_19),
% 0.22/0.56    inference(avatar_component_clause,[],[f240])).
% 0.22/0.56  fof(f243,plain,(
% 0.22/0.56    ~spl7_19 | ~spl7_6 | ~spl7_8 | ~spl7_17),
% 0.22/0.56    inference(avatar_split_clause,[],[f238,f231,f147,f139,f240])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    spl7_17 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~spl7_17),
% 0.22/0.56    inference(resolution,[],[f232,f51])).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_17),
% 0.22/0.56    inference(avatar_component_clause,[],[f231])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    spl7_17 | spl7_18 | ~spl7_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f229,f210,f234,f231])).
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_14),
% 0.22/0.56    inference(resolution,[],[f216,f64])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) | ~spl7_14),
% 0.22/0.56    inference(superposition,[],[f101,f212])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f66,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f67,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f68,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f70,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f74,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f75,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f76,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    spl7_14 | spl7_3 | ~spl7_8 | ~spl7_6 | spl7_5 | ~spl7_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f208,f205,f135,f139,f147,f125,f210])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    spl7_3 <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.56  fof(f205,plain,(
% 0.22/0.56    spl7_13 <=> ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK4,X0) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    v2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_13),
% 0.22/0.56    inference(resolution,[],[f206,f56])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_pre_topc(sK4,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f205])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    spl7_7 | spl7_9 | spl7_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f203,f205,f151,f143])).
% 0.22/0.56  fof(f203,plain,(
% 0.22/0.56    ( ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k6_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f202,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ~r1_tsep_1(sK3,sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f200,f73])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f199])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f104,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f100])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f62,f98])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    ~spl7_9),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    $false | ~spl7_9),
% 0.22/0.56    inference(resolution,[],[f153,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ~v2_struct_0(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    v2_struct_0(sK4) | ~spl7_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f151])).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    ~spl7_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    $false | ~spl7_7),
% 0.22/0.56    inference(resolution,[],[f145,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ~v2_struct_0(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    v2_struct_0(sK3) | ~spl7_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f143])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    ~spl7_5),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    $false | ~spl7_5),
% 0.22/0.56    inference(resolution,[],[f137,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ~v2_struct_0(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    v2_struct_0(sK2) | ~spl7_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f135])).
% 0.22/0.56  fof(f165,plain,(
% 0.22/0.56    spl7_10),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f164])).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    $false | spl7_10),
% 0.22/0.56    inference(resolution,[],[f157,f56])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ~m1_pre_topc(sK4,sK2) | spl7_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f155])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    spl7_8),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    $false | spl7_8),
% 0.22/0.56    inference(resolution,[],[f149,f54])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    ~m1_pre_topc(sK3,sK2) | spl7_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f147])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    spl7_6),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    $false | spl7_6),
% 0.22/0.56    inference(resolution,[],[f141,f52])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    ~l1_pre_topc(sK2) | spl7_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f139])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | ~spl7_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f133,f125,f155,f151,f147,f143,f139,f135])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl7_3),
% 0.22/0.56    inference(resolution,[],[f71,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~spl7_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f125])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl7_3 | spl7_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f123,f129,f125])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f61,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ~spl7_1 | ~spl7_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f103,f119,f115])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.56    inference(equality_resolution,[],[f102])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X5] : (~m1_subset_1(sK5,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 0.22/0.56    inference(equality_resolution,[],[f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X4,X5] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (20105)------------------------------
% 0.22/0.56  % (20105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20105)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (20105)Memory used [KB]: 6524
% 0.22/0.56  % (20105)Time elapsed: 0.146 s
% 0.22/0.56  % (20105)------------------------------
% 0.22/0.56  % (20105)------------------------------
% 0.22/0.56  % (20085)Success in time 0.203 s
%------------------------------------------------------------------------------
