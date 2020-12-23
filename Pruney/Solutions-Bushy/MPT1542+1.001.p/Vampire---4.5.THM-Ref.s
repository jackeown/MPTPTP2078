%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1542+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 591 expanded)
%              Number of leaves         :   49 ( 298 expanded)
%              Depth                    :   11
%              Number of atoms          : 1272 (4515 expanded)
%              Number of equality atoms :   15 (  77 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f83,f87,f91,f102,f110,f112,f117,f134,f144,f148,f160,f166,f171,f180,f210,f243,f249,f259,f269,f287,f292,f294,f296,f298,f299,f311,f351,f359,f361,f363,f365,f368,f374,f383])).

fof(f383,plain,
    ( ~ spl8_9
    | ~ spl8_14
    | ~ spl8_5
    | spl8_15 ),
    inference(avatar_split_clause,[],[f380,f132,f81,f129,f105])).

fof(f105,plain,
    ( spl8_9
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f129,plain,
    ( spl8_14
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f81,plain,
    ( spl8_5
  <=> ! [X3,X4] :
        ( r1_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f132,plain,
    ( spl8_15
  <=> r1_yellow_0(sK0,k2_tarski(sK3(sK0),sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f380,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ spl8_5
    | spl8_15 ),
    inference(resolution,[],[f133,f82])).

fof(f82,plain,
    ( ! [X4,X3] :
        ( r1_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f133,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK3(sK0),sK4(sK0)))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f374,plain,
    ( ~ spl8_6
    | ~ spl8_13
    | ~ spl8_53
    | ~ spl8_54
    | spl8_1
    | spl8_52 ),
    inference(avatar_split_clause,[],[f373,f349,f65,f357,f354,f126,f85])).

fof(f85,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f126,plain,
    ( spl8_13
  <=> m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f354,plain,
    ( spl8_53
  <=> r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f357,plain,
    ( spl8_54
  <=> r1_orders_2(sK0,sK4(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f65,plain,
    ( spl8_1
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f349,plain,
    ( spl8_52
  <=> r1_orders_2(sK0,sK3(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f373,plain,
    ( v1_lattice3(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_52 ),
    inference(resolution,[],[f350,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( r1_orders_2(X0,sK3(X0),sK5(X0,X3))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
                  & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
                  & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
                  & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,sK6(X0,X5,X6))
                    & r1_orders_2(X0,X5,sK6(X0,X5,X6))
                    & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f28,f27,f26,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK3(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,sK3(X0),X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,sK3(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK4(X0),X4)
                & r1_orders_2(X0,sK3(X0),X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,sK3(X0),X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,sK4(X0),X4)
          & r1_orders_2(X0,sK3(X0),X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5(X0,X3))
        & r1_orders_2(X0,sK4(X0),sK5(X0,X3))
        & r1_orders_2(X0,sK3(X0),sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK6(X0,X5,X6))
        & r1_orders_2(X0,X5,sK6(X0,X5,X6))
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X7,X8)
                          | ~ r1_orders_2(X0,X6,X8)
                          | ~ r1_orders_2(X0,X5,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X6,X7)
                      & r1_orders_2(X0,X5,X7)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

fof(f350,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | spl8_52 ),
    inference(avatar_component_clause,[],[f349])).

fof(f368,plain,
    ( ~ spl8_54
    | ~ spl8_53
    | ~ spl8_13
    | ~ spl8_45
    | spl8_51 ),
    inference(avatar_split_clause,[],[f366,f346,f309,f126,f354,f357])).

fof(f309,plain,
    ( spl8_45
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK4(sK0),sK5(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0),X0)
        | ~ r1_orders_2(sK0,sK4(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f346,plain,
    ( spl8_51
  <=> r1_orders_2(sK0,sK4(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f366,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ r1_orders_2(sK0,sK4(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ spl8_45
    | spl8_51 ),
    inference(resolution,[],[f310,f347])).

fof(f347,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | spl8_51 ),
    inference(avatar_component_clause,[],[f346])).

fof(f310,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK4(sK0),sK5(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0),X0)
        | ~ r1_orders_2(sK0,sK4(sK0),X0) )
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f309])).

fof(f365,plain,
    ( ~ spl8_14
    | ~ spl8_9
    | ~ spl8_5
    | ~ spl8_8
    | spl8_54 ),
    inference(avatar_split_clause,[],[f364,f357,f100,f81,f105,f129])).

fof(f100,plain,
    ( spl8_8
  <=> ! [X1,X0] :
        ( ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | r1_orders_2(sK0,X0,k10_lattice3(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f364,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl8_5
    | ~ spl8_8
    | spl8_54 ),
    inference(resolution,[],[f358,f324])).

fof(f324,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,k10_lattice3(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f101,f82])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,k10_lattice3(sK0,X0,X1))
        | ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f358,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | spl8_54 ),
    inference(avatar_component_clause,[],[f357])).

fof(f363,plain,
    ( ~ spl8_14
    | ~ spl8_9
    | ~ spl8_5
    | ~ spl8_11
    | spl8_53 ),
    inference(avatar_split_clause,[],[f362,f354,f115,f81,f105,f129])).

fof(f115,plain,
    ( spl8_11
  <=> ! [X1,X0] :
        ( ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | r1_orders_2(sK0,X1,k10_lattice3(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f362,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl8_5
    | ~ spl8_11
    | spl8_53 ),
    inference(resolution,[],[f355,f323])).

fof(f323,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k10_lattice3(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f116,f82])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k10_lattice3(sK0,X0,X1))
        | ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f355,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | spl8_53 ),
    inference(avatar_component_clause,[],[f354])).

fof(f361,plain,
    ( ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | spl8_13 ),
    inference(avatar_split_clause,[],[f360,f126,f129,f105,f85])).

fof(f360,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_13 ),
    inference(resolution,[],[f127,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f127,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f359,plain,
    ( ~ spl8_6
    | ~ spl8_13
    | ~ spl8_53
    | ~ spl8_54
    | spl8_1
    | spl8_50 ),
    inference(avatar_split_clause,[],[f352,f343,f65,f357,f354,f126,f85])).

fof(f343,plain,
    ( spl8_50
  <=> m1_subset_1(sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f352,plain,
    ( v1_lattice3(sK0)
    | ~ r1_orders_2(sK0,sK4(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_50 ),
    inference(resolution,[],[f344,f44])).

fof(f44,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f344,plain,
    ( ~ m1_subset_1(sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))),u1_struct_0(sK0))
    | spl8_50 ),
    inference(avatar_component_clause,[],[f343])).

fof(f351,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_14
    | ~ spl8_50
    | ~ spl8_51
    | ~ spl8_52
    | ~ spl8_15
    | spl8_12 ),
    inference(avatar_split_clause,[],[f341,f123,f132,f349,f346,f343,f129,f105,f85,f89])).

fof(f89,plain,
    ( spl8_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f123,plain,
    ( spl8_12
  <=> r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f341,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK3(sK0),sK4(sK0)))
    | ~ r1_orders_2(sK0,sK3(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ r1_orders_2(sK0,sK4(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ m1_subset_1(sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_12 ),
    inference(forward_demodulation,[],[f340,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f340,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ r1_orders_2(sK0,sK4(sK0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ m1_subset_1(sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_12 ),
    inference(resolution,[],[f124,f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f61,f60])).

fof(f61,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f30])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f124,plain,
    ( ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f311,plain,
    ( spl8_1
    | spl8_45
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f155,f85,f309,f65])).

fof(f155,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK4(sK0),sK5(sK0,X0))
        | ~ r1_orders_2(sK0,sK4(sK0),X0)
        | ~ r1_orders_2(sK0,sK3(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_lattice3(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f46,f86])).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f46,plain,(
    ! [X0,X3] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK4(X0),sK5(X0,X3))
      | ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f299,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_14 ),
    inference(avatar_split_clause,[],[f185,f129,f65,f85])).

fof(f185,plain,
    ( v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_14 ),
    inference(resolution,[],[f130,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f130,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f298,plain,
    ( ~ spl8_4
    | ~ spl8_3
    | ~ spl8_17
    | spl8_41 ),
    inference(avatar_split_clause,[],[f297,f285,f142,f72,f76])).

fof(f76,plain,
    ( spl8_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f72,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f142,plain,
    ( spl8_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f285,plain,
    ( spl8_41
  <=> r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f297,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_17
    | spl8_41 ),
    inference(resolution,[],[f286,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK6(sK0,X1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f286,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2))
    | spl8_41 ),
    inference(avatar_component_clause,[],[f285])).

fof(f296,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | ~ spl8_18
    | spl8_42 ),
    inference(avatar_split_clause,[],[f295,f290,f146,f76,f72])).

fof(f146,plain,
    ( spl8_18
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK6(sK0,X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f290,plain,
    ( spl8_42
  <=> r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f295,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_18
    | spl8_42 ),
    inference(resolution,[],[f291,f147])).

fof(f147,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X3,sK6(sK0,X3,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f291,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f290])).

fof(f294,plain,
    ( ~ spl8_6
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_3
    | spl8_40 ),
    inference(avatar_split_clause,[],[f293,f282,f72,f76,f65,f85])).

fof(f282,plain,
    ( spl8_40
  <=> m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f293,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_40 ),
    inference(resolution,[],[f283,f38])).

fof(f38,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f283,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_40 ),
    inference(avatar_component_clause,[],[f282])).

fof(f292,plain,
    ( ~ spl8_41
    | ~ spl8_42
    | ~ spl8_40
    | ~ spl8_3
    | ~ spl8_4
    | spl8_2
    | ~ spl8_19
    | spl8_39 ),
    inference(avatar_split_clause,[],[f288,f279,f158,f68,f76,f72,f282,f290,f285])).

fof(f68,plain,
    ( spl8_2
  <=> r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f158,plain,
    ( spl8_19
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f279,plain,
    ( spl8_39
  <=> r1_orders_2(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f288,plain,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2))
    | ~ spl8_19
    | spl8_39 ),
    inference(resolution,[],[f280,f159])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f280,plain,
    ( ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)))
    | spl8_39 ),
    inference(avatar_component_clause,[],[f279])).

fof(f287,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | ~ spl8_39
    | ~ spl8_40
    | ~ spl8_41
    | ~ spl8_18
    | ~ spl8_37 ),
    inference(avatar_split_clause,[],[f277,f267,f146,f285,f282,f279,f76,f72])).

fof(f267,plain,
    ( spl8_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,sK2))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f277,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_18
    | ~ spl8_37 ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_18
    | ~ spl8_37 ),
    inference(resolution,[],[f268,f147])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,sK2))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f267])).

fof(f269,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_2
    | spl8_37
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f265,f257,f164,f267,f68,f76,f72])).

fof(f164,plain,
    ( spl8_20
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X1,X0,X2))
        | r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f257,plain,
    ( spl8_35
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,sK2)) )
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,sK2)) )
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(resolution,[],[f258,f165])).

fof(f165,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X1,X0,X2))
        | r1_yellow_0(sK0,k2_tarski(X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f164])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2))) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl8_35
    | ~ spl8_3
    | ~ spl8_17
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f255,f247,f142,f72,f257])).

fof(f247,plain,
    ( spl8_34
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_17
    | ~ spl8_34 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,sK2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ r1_orders_2(sK0,sK2,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_17
    | ~ spl8_34 ),
    inference(resolution,[],[f248,f143])).

fof(f248,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( ~ spl8_6
    | ~ spl8_1
    | spl8_34
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f245,f241,f247,f65,f85])).

fof(f241,plain,
    ( spl8_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_33 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_33 ),
    inference(resolution,[],[f242,f38])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_3
    | spl8_2
    | spl8_33
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f239,f208,f241,f68,f72,f76,f85,f89])).

fof(f208,plain,
    ( spl8_28
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_28 ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_28 ),
    inference(resolution,[],[f209,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1)) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( ~ spl8_6
    | ~ spl8_1
    | spl8_28
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f188,f178,f208,f65,f85])).

fof(f178,plain,
    ( spl8_22
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2,sK6(sK0,X0,X1))
        | ~ r1_orders_2(sK0,sK1,sK6(sK0,X0,X1))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_22 ),
    inference(resolution,[],[f179,f41])).

fof(f41,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK6(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,X0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_22
    | spl8_2
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f173,f169,f68,f178,f76,f72])).

fof(f169,plain,
    ( spl8_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X1,X2,X0))
        | r1_yellow_0(sK0,k2_tarski(X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | spl8_2
    | ~ spl8_21 ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( r1_yellow_0(sK0,k2_tarski(X1,X2))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,X1,X2,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( ~ spl8_6
    | spl8_21
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f167,f89,f169,f85])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,k2_tarski(X1,X2)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f58,f90])).

fof(f90,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f166,plain,
    ( ~ spl8_6
    | spl8_20
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f162,f89,f164,f85])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X1,X0,X2))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,k2_tarski(X1,X0)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f57,f90])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f160,plain,
    ( ~ spl8_6
    | spl8_19
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f156,f89,f158,f85])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_yellow_0(sK0,k2_tarski(X0,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f56,f90])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f148,plain,
    ( ~ spl8_6
    | spl8_18
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f140,f65,f146,f85])).

fof(f140,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK6(sK0,X3,X2))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,sK6(X0,X5,X6))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,
    ( v1_lattice3(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f144,plain,
    ( ~ spl8_6
    | spl8_17
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f139,f65,f142,f85])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,X1,X0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X6,X0,X5] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X6,sK6(X0,X5,X6))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f134,plain,
    ( ~ spl8_12
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_9
    | ~ spl8_15
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f121,f115,f108,f132,f105,f129,f126,f123])).

fof(f108,plain,
    ( spl8_10
  <=> ! [X0] :
        ( ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),X0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),X0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f121,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK3(sK0),sK4(sK0)))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f120,f59])).

fof(f120,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0)),sK5(sK0,k10_lattice3(sK0,sK4(sK0),sK3(sK0))))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f116,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),X0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),X0),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),X0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f117,plain,
    ( ~ spl8_6
    | spl8_11
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f113,f89,f115,f85])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X1,k10_lattice3(sK0,X0,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f93,f90])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f62,f60])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f111,f105,f65,f85])).

fof(f111,plain,
    ( v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_9 ),
    inference(resolution,[],[f106,f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f110,plain,
    ( ~ spl8_6
    | spl8_1
    | ~ spl8_9
    | spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f103,f100,f108,f105,f65,f85])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k10_lattice3(sK0,sK4(sK0),X0),sK5(sK0,k10_lattice3(sK0,sK4(sK0),X0)))
        | v1_lattice3(sK0)
        | ~ r1_orders_2(sK0,sK3(sK0),k10_lattice3(sK0,sK4(sK0),X0))
        | ~ m1_subset_1(k10_lattice3(sK0,sK4(sK0),X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,sK4(X0),X3)
      | ~ r1_orders_2(X0,X3,sK5(X0,X3))
      | v1_lattice3(X0)
      | ~ r1_orders_2(X0,sK3(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,
    ( ~ spl8_6
    | spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f97,f89,f100,f85])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r1_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X0,k10_lattice3(sK0,X0,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f92,f90])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f63,f60])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
        & m1_subset_1(sK2,u1_struct_0(sK0))
        & m1_subset_1(sK1,u1_struct_0(sK0)) )
      | ~ v1_lattice3(sK0) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r1_yellow_0(sK0,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v1_lattice3(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r1_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v1_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            & m1_subset_1(X1,u1_struct_0(sK0)) )
        | ~ v1_lattice3(sK0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(sK0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v1_lattice3(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_yellow_0(sK0,k2_tarski(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ r1_yellow_0(sK0,k2_tarski(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r1_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v1_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v1_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v1_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v1_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

fof(f87,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f34,f81,f65])).

fof(f34,plain,(
    ! [X4,X3] :
      ( r1_yellow_0(sK0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v1_lattice3(sK0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f35,f76,f65])).

fof(f35,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f36,f72,f65])).

fof(f36,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f37,f68,f65])).

fof(f37,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
