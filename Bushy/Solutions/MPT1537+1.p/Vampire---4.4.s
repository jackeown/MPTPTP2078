%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t15_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:37 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 761 expanded)
%              Number of leaves         :   47 ( 353 expanded)
%              Depth                    :   15
%              Number of atoms          : 1500 (5638 expanded)
%              Number of equality atoms :   58 ( 274 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f84,f111,f118,f123,f128,f133,f138,f144,f187,f195,f211,f223,f235,f265,f272,f288,f292,f296,f300,f346,f371,f386,f390,f411,f415,f465,f483,f486,f491,f513,f523,f527,f583,f597,f606,f691])).

fof(f691,plain,
    ( spl11_58
    | ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f660,f366,f116,f109,f100,f82,f335])).

fof(f335,plain,
    ( spl11_58
  <=> r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f82,plain,
    ( spl11_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f100,plain,
    ( spl11_9
  <=> ~ r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f109,plain,
    ( spl11_10
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f116,plain,
    ( spl11_12
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f366,plain,
    ( spl11_66
  <=> sK3 = sK4(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f660,plain,
    ( r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f659,f83])).

fof(f83,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f659,plain,
    ( r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f658,f110])).

fof(f110,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f658,plain,
    ( r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f657,f117])).

fof(f117,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f657,plain,
    ( r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f636,f101])).

fof(f101,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f636,plain,
    ( r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_66 ),
    inference(trivial_inequality_removal,[],[f635])).

fof(f635,plain,
    ( sK3 != sK3
    | r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_66 ),
    inference(superposition,[],[f65,f367])).

fof(f367,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f366])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK4(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,sK4(X0,X1,X2),X4)
                      | ~ r2_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK6(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,X7,sK7(X0,X1,X7))
                    & r2_lattice3(X0,X1,sK7(X0,X1,X7))
                    & m1_subset_1(sK7(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,sK6(X0,X1),X9)
                  | ~ r2_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f32,f31,f30,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X3,X4)
              | ~ r2_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK4(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,sK4(X0,X1,X2),X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X5)
          & r2_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X7,X8)
                  & r2_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X6,X9)
              | ~ r2_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK6(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X7,X8)
                & r2_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,sK6(X0,X1),X9)
            | ~ r2_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X7,X8)
          & r2_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X7,sK7(X0,X1,X7))
        & r2_lattice3(X0,X1,sK7(X0,X1,X7))
        & m1_subset_1(sK7(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X7,X8)
                        & r2_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X6,X9)
                    | ~ r2_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( X2 = X3
                    | ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r2_lattice3(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t15_yellow_0.p',d7_yellow_0)).

fof(f606,plain,
    ( ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_57
    | spl11_71 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_71 ),
    inference(subsumption_resolution,[],[f604,f83])).

fof(f604,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_71 ),
    inference(subsumption_resolution,[],[f603,f110])).

fof(f603,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_71 ),
    inference(subsumption_resolution,[],[f602,f117])).

fof(f602,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_57
    | ~ spl11_71 ),
    inference(subsumption_resolution,[],[f601,f333])).

fof(f333,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_57 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl11_57
  <=> ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f601,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_71 ),
    inference(subsumption_resolution,[],[f599,f101])).

fof(f599,plain,
    ( r1_yellow_0(sK0,sK1)
    | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_71 ),
    inference(resolution,[],[f407,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f407,plain,
    ( ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_71 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl11_71
  <=> ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_71])])).

fof(f597,plain,
    ( ~ spl11_71
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_60
    | spl11_67
    | ~ spl11_96 ),
    inference(avatar_split_clause,[],[f590,f581,f369,f344,f136,f116,f109,f406])).

fof(f136,plain,
    ( spl11_20
  <=> ! [X5] :
        ( r1_orders_2(sK0,sK3,X5)
        | ~ r2_lattice3(sK0,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f344,plain,
    ( spl11_60
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_60])])).

fof(f369,plain,
    ( spl11_67
  <=> sK3 != sK4(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_67])])).

fof(f581,plain,
    ( spl11_96
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_96])])).

fof(f590,plain,
    ( ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_60
    | ~ spl11_67
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f589,f345])).

fof(f345,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_60 ),
    inference(avatar_component_clause,[],[f344])).

fof(f589,plain,
    ( ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_67
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f588,f370])).

fof(f370,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | ~ spl11_67 ),
    inference(avatar_component_clause,[],[f369])).

fof(f588,plain,
    ( sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_20
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f587,f117])).

fof(f587,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_96 ),
    inference(subsumption_resolution,[],[f584,f110])).

fof(f584,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_20
    | ~ spl11_96 ),
    inference(resolution,[],[f582,f137])).

fof(f137,plain,
    ( ! [X5] :
        ( r1_orders_2(sK0,sK3,X5)
        | ~ r2_lattice3(sK0,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_96 ),
    inference(avatar_component_clause,[],[f581])).

fof(f583,plain,
    ( spl11_96
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_57
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(avatar_split_clause,[],[f546,f489,f344,f332,f116,f109,f100,f581])).

fof(f489,plain,
    ( spl11_84
  <=> ! [X1,X0,X2] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,X1,sK4(sK0,X0,X2))
        | ~ m1_subset_1(sK4(sK0,X0,X2),u1_struct_0(sK0))
        | sK4(sK0,X0,X2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f546,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(subsumption_resolution,[],[f545,f101])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(subsumption_resolution,[],[f544,f110])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_12
    | ~ spl11_57
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(subsumption_resolution,[],[f543,f117])).

fof(f543,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_57
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(subsumption_resolution,[],[f542,f333])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK3))
        | ~ r2_lattice3(sK0,sK1,X0)
        | sK4(sK0,sK1,sK3) = X0 )
    | ~ spl11_60
    | ~ spl11_84 ),
    inference(resolution,[],[f345,f490])).

fof(f490,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,X1,sK4(sK0,X0,X2))
        | ~ r2_lattice3(sK0,X0,X1)
        | sK4(sK0,X0,X2) = X1 )
    | ~ spl11_84 ),
    inference(avatar_component_clause,[],[f489])).

fof(f527,plain,
    ( ~ spl11_57
    | spl11_72
    | spl11_9
    | ~ spl11_12
    | ~ spl11_58
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f526,f388,f335,f116,f100,f413,f332])).

fof(f413,plain,
    ( spl11_72
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f388,plain,
    ( spl11_68
  <=> ! [X1,X0] :
        ( r1_orders_2(sK0,sK4(sK0,X0,sK3),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f526,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) )
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_58
    | ~ spl11_68 ),
    inference(subsumption_resolution,[],[f392,f336])).

fof(f336,plain,
    ( r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ spl11_58 ),
    inference(avatar_component_clause,[],[f335])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
        | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) )
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_68 ),
    inference(subsumption_resolution,[],[f391,f101])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1)
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
        | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) )
    | ~ spl11_12
    | ~ spl11_68 ),
    inference(resolution,[],[f389,f117])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,sK4(sK0,X0,sK3),X1)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f388])).

fof(f523,plain,
    ( ~ spl11_20
    | ~ spl11_56
    | ~ spl11_58
    | spl11_87 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl11_20
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f521,f330])).

fof(f330,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl11_56
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f521,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_20
    | ~ spl11_58
    | ~ spl11_87 ),
    inference(subsumption_resolution,[],[f519,f336])).

fof(f519,plain,
    ( ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_20
    | ~ spl11_87 ),
    inference(resolution,[],[f512,f137])).

fof(f512,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl11_87 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl11_87
  <=> ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f513,plain,
    ( ~ spl11_87
    | ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f504,f366,f116,f109,f100,f82,f511])).

fof(f504,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f503,f83])).

fof(f503,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f502,f110])).

fof(f502,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f501,f117])).

fof(f501,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_66 ),
    inference(subsumption_resolution,[],[f500,f101])).

fof(f500,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_66 ),
    inference(trivial_inequality_removal,[],[f497])).

fof(f497,plain,
    ( sK3 != sK3
    | r1_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_66 ),
    inference(superposition,[],[f66,f367])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f491,plain,
    ( spl11_84
    | ~ spl11_34
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f307,f286,f221,f489])).

fof(f221,plain,
    ( spl11_34
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f286,plain,
    ( spl11_48
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f307,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,X1,sK4(sK0,X0,X2))
        | ~ m1_subset_1(sK4(sK0,X0,X2),u1_struct_0(sK0))
        | sK4(sK0,X0,X2) = X1 )
    | ~ spl11_34
    | ~ spl11_48 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,X1,sK4(sK0,X0,X2))
        | ~ m1_subset_1(sK4(sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK4(sK0,X0,X2) = X1 )
    | ~ spl11_34
    | ~ spl11_48 ),
    inference(resolution,[],[f287,f222])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 )
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f221])).

fof(f287,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f286])).

fof(f486,plain,
    ( spl11_9
    | ~ spl11_12
    | ~ spl11_54
    | ~ spl11_56
    | ~ spl11_58
    | spl11_71 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_54
    | ~ spl11_56
    | ~ spl11_58
    | ~ spl11_71 ),
    inference(unit_resulting_resolution,[],[f101,f117,f330,f336,f407,f299])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK3)
        | r2_lattice3(sK0,X0,sK4(sK0,X0,sK3))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_54 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl11_54
  <=> ! [X0] :
        ( r2_lattice3(sK0,X0,sK4(sK0,X0,sK3))
        | ~ r2_lattice3(sK0,X0,sK3)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f483,plain,
    ( ~ spl11_71
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_36
    | ~ spl11_60
    | spl11_67
    | ~ spl11_72 ),
    inference(avatar_split_clause,[],[f472,f413,f369,f344,f233,f116,f109,f406])).

fof(f233,plain,
    ( spl11_36
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = X0
        | ~ r2_lattice3(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f472,plain,
    ( ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_36
    | ~ spl11_60
    | ~ spl11_67
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f454,f345])).

fof(f454,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_36
    | ~ spl11_67
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f453,f370])).

fof(f453,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_36
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f452,f117])).

fof(f452,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_10
    | ~ spl11_36
    | ~ spl11_72 ),
    inference(subsumption_resolution,[],[f446,f110])).

fof(f446,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK3 = sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_36
    | ~ spl11_72 ),
    inference(resolution,[],[f414,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = X0
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f414,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f413])).

fof(f465,plain,
    ( ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_59
    | spl11_61 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_59
    | ~ spl11_61 ),
    inference(unit_resulting_resolution,[],[f83,f101,f110,f117,f339,f342,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f342,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_61 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl11_61
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f339,plain,
    ( ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl11_59
  <=> ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f415,plain,
    ( spl11_72
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_52
    | spl11_59 ),
    inference(avatar_split_clause,[],[f404,f338,f294,f116,f109,f100,f413])).

fof(f294,plain,
    ( spl11_52
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0) )
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_52
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f324,f339])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0) )
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f323,f101])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | r1_yellow_0(sK0,sK1) )
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f314,f110])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
        | r1_orders_2(sK0,sK4(sK0,sK1,sK3),X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,sK1) )
    | ~ spl11_12
    | ~ spl11_52 ),
    inference(resolution,[],[f295,f117])).

fof(f295,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK5(sK0,X0,X1))
        | r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f294])).

fof(f411,plain,
    ( spl11_70
    | ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_59 ),
    inference(avatar_split_clause,[],[f399,f338,f116,f109,f100,f82,f409])).

fof(f409,plain,
    ( spl11_70
  <=> r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f399,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f398,f83])).

fof(f398,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f397,f110])).

fof(f397,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f396,f117])).

fof(f396,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_59 ),
    inference(subsumption_resolution,[],[f394,f101])).

fof(f394,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_59 ),
    inference(resolution,[],[f339,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f390,plain,
    ( spl11_68
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f268,f136,f109,f82,f388])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,sK3),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f267,f83])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,sK3),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_10
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f266,f110])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,sK3),X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_20 ),
    inference(resolution,[],[f63,f137])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f386,plain,
    ( spl11_60
    | ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_57 ),
    inference(avatar_split_clause,[],[f356,f332,f116,f109,f100,f82,f344])).

fof(f356,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f355,f83])).

fof(f355,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f354,f110])).

fof(f354,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f353,f117])).

fof(f353,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f351,f101])).

fof(f351,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_57 ),
    inference(resolution,[],[f333,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f371,plain,
    ( ~ spl11_67
    | ~ spl11_2
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | spl11_57 ),
    inference(avatar_split_clause,[],[f360,f332,f116,f109,f100,f82,f369])).

fof(f360,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | ~ spl11_2
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f359,f83])).

fof(f359,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f358,f110])).

fof(f358,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f357,f117])).

fof(f357,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_9
    | ~ spl11_57 ),
    inference(subsumption_resolution,[],[f352,f101])).

fof(f352,plain,
    ( sK3 != sK4(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_57 ),
    inference(resolution,[],[f333,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | sK4(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f346,plain,
    ( ~ spl11_57
    | ~ spl11_59
    | spl11_60
    | spl11_9
    | ~ spl11_12
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f313,f290,f116,f100,f344,f338,f332])).

fof(f290,plain,
    ( spl11_50
  <=> ! [X0] :
        ( m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f313,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_9
    | ~ spl11_12
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f312,f101])).

fof(f312,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK5(sK0,sK1,sK3))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl11_12
    | ~ spl11_50 ),
    inference(resolution,[],[f291,f117])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK3)
        | m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f290])).

fof(f300,plain,
    ( spl11_54
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_42 ),
    inference(avatar_split_clause,[],[f276,f270,f136,f109,f298])).

fof(f270,plain,
    ( spl11_42
  <=> ! [X1,X0] :
        ( r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,sK4(sK0,X0,sK3))
        | ~ r2_lattice3(sK0,X0,sK3)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f275,f110])).

fof(f275,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,sK4(sK0,X0,sK3))
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_42 ),
    inference(resolution,[],[f271,f137])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f270])).

fof(f296,plain,
    ( spl11_52
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f260,f82,f294])).

fof(f260,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f62,f83])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f292,plain,
    ( spl11_50
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f274,f263,f136,f109,f290])).

fof(f263,plain,
    ( spl11_40
  <=> ! [X1,X0] :
        ( m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f274,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3)
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f273,f110])).

fof(f273,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,X0,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0)
        | ~ r2_lattice3(sK0,sK1,sK5(sK0,X0,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(resolution,[],[f264,f137])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f263])).

fof(f288,plain,
    ( spl11_48
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f256,f82,f286])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK4(sK0,X0,X1),X2)
        | ~ r2_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f61,f83])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK4(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f272,plain,
    ( spl11_42
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f249,f82,f270])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f60,f83])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f265,plain,
    ( spl11_40
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f230,f82,f263])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_2 ),
    inference(resolution,[],[f57,f83])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f235,plain,
    ( spl11_36
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f228,f221,f136,f109,f233])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = X0
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl11_10
    | ~ spl11_20
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f227,f110])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = X0
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl11_20
    | ~ spl11_34 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = X0
        | ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_34 ),
    inference(resolution,[],[f222,f137])).

fof(f223,plain,
    ( spl11_34
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f162,f82,f75,f221])).

fof(f75,plain,
    ( spl11_0
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 )
    | ~ spl11_0
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f161,f83])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl11_0 ),
    inference(resolution,[],[f67,f76])).

fof(f76,plain,
    ( v5_orders_2(sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f75])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t15_yellow_0.p',t25_orders_2)).

fof(f211,plain,
    ( ~ spl11_2
    | ~ spl11_8
    | spl11_31 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_8
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f209,f83])).

fof(f209,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_8
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f207,f104])).

fof(f104,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_8
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f207,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl11_31 ),
    inference(resolution,[],[f186,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f186,plain,
    ( ~ r2_lattice3(sK0,sK1,sK6(sK0,sK1))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_31
  <=> ~ r2_lattice3(sK0,sK1,sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f195,plain,
    ( ~ spl11_9
    | ~ spl11_2
    | spl11_29 ),
    inference(avatar_split_clause,[],[f194,f179,f82,f100])).

fof(f179,plain,
    ( spl11_29
  <=> ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f194,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl11_2
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f189,f83])).

fof(f189,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl11_29 ),
    inference(resolution,[],[f180,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f180,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f179])).

fof(f187,plain,
    ( ~ spl11_29
    | ~ spl11_31
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f174,f142,f131,f126,f121,f185,f179])).

fof(f121,plain,
    ( spl11_14
  <=> ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f126,plain,
    ( spl11_16
  <=> ! [X2] :
        ( r2_lattice3(sK0,sK1,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f131,plain,
    ( spl11_18
  <=> ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f142,plain,
    ( spl11_22
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f174,plain,
    ( ~ r2_lattice3(sK0,sK1,sK6(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f173,f127])).

fof(f127,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK1,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f173,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK6(sK0,sK1)))
    | ~ r2_lattice3(sK0,sK1,sK6(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f172,f122])).

fof(f122,plain,
    ( ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f172,plain,
    ( ~ m1_subset_1(sK2(sK6(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK2(sK6(sK0,sK1)))
    | ~ r2_lattice3(sK0,sK1,sK6(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_18
    | ~ spl11_22 ),
    inference(resolution,[],[f143,f132])).

fof(f132,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f143,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK6(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X0) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( spl11_22
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f140,f103,f82,f142])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK1),X0) )
    | ~ spl11_2
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f139,f83])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK1),X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f51,f104])).

fof(f51,plain,(
    ! [X0,X1,X9] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | r1_orders_2(X0,sK6(X0,X1),X9)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,
    ( spl11_20
    | spl11_9 ),
    inference(avatar_split_clause,[],[f134,f100,f136])).

fof(f134,plain,
    ( ! [X5] :
        ( r1_orders_2(sK0,sK3,X5)
        | ~ r2_lattice3(sK0,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f44,f101])).

fof(f44,plain,(
    ! [X5] :
      ( r1_orders_2(sK0,sK3,X5)
      | ~ r2_lattice3(sK0,sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ! [X2] :
          ( ( ~ r1_orders_2(sK0,X2,sK2(X2))
            & r2_lattice3(sK0,sK1,sK2(X2))
            & m1_subset_1(sK2(X2),u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,sK1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      | ~ r1_yellow_0(sK0,sK1) )
    & ( ( ! [X5] :
            ( r1_orders_2(sK0,sK3,X5)
            | ~ r2_lattice3(sK0,sK1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK1,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | r1_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      & r2_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r1_yellow_0(X0,X1) )
            & ( ? [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X4,X5)
                      | ~ r2_lattice3(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(sK0,X2,X3)
                    & r2_lattice3(sK0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ r2_lattice3(sK0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r1_yellow_0(sK0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(sK0,X4,X5)
                    | ~ r2_lattice3(sK0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                & r2_lattice3(sK0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | r1_yellow_0(sK0,X1) ) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
     => ( ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,sK1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,sK1) )
        & ( ? [X4] :
              ( ! [X5] :
                  ( r1_orders_2(X0,X4,X5)
                  | ~ r2_lattice3(X0,sK1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,sK1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | r1_yellow_0(X0,sK1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X2))
        & r2_lattice3(X0,X1,sK2(X2))
        & m1_subset_1(sK2(X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK3,X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK3)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( r1_yellow_0(X0,X1)
          <=> ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t15_yellow_0.p',t15_yellow_0)).

fof(f133,plain,
    ( spl11_18
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f129,f103,f131])).

fof(f129,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f47,f104])).

fof(f47,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,X2,sK2(X2))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( spl11_16
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f124,f103,f126])).

fof(f124,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK1,sK2(X2))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f46,f104])).

fof(f46,plain,(
    ! [X2] :
      ( r2_lattice3(sK0,sK1,sK2(X2))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f123,plain,
    ( spl11_14
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f119,f103,f121])).

fof(f119,plain,
    ( ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f45,f104])).

fof(f45,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,
    ( spl11_8
    | spl11_12 ),
    inference(avatar_split_clause,[],[f43,f116,f103])).

fof(f43,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,
    ( spl11_8
    | spl11_10 ),
    inference(avatar_split_clause,[],[f42,f109,f103])).

fof(f42,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
