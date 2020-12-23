%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1538+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 3.54s
% Output     : Refutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 695 expanded)
%              Number of leaves         :   32 ( 327 expanded)
%              Depth                    :   18
%              Number of atoms          : 1214 (5213 expanded)
%              Number of equality atoms :   46 ( 255 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3094,f3098,f3102,f3107,f3111,f3115,f3119,f3123,f4409,f4576,f4617,f4628,f4632,f4635,f4780,f5062,f5069,f5072,f5377,f5415,f5429,f5440,f5444,f5483,f5619,f5622,f5656,f5662])).

fof(f5662,plain,
    ( spl11_45
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(avatar_split_clause,[],[f5660,f4583,f3117,f3113,f3109,f3089,f4553])).

fof(f4553,plain,
    ( spl11_45
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f3089,plain,
    ( spl11_1
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f3109,plain,
    ( spl11_6
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f3113,plain,
    ( spl11_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f3117,plain,
    ( spl11_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f4583,plain,
    ( spl11_49
  <=> m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f5660,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5659,f3118])).

fof(f3118,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f3117])).

fof(f5659,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5658,f3114])).

fof(f3114,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f3113])).

fof(f5658,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5657,f3110])).

fof(f3110,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f3109])).

fof(f5657,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5646,f3090])).

fof(f3090,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f5646,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_49 ),
    inference(resolution,[],[f4584,f3071])).

fof(f3071,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f3030,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK6(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,sK6(X0,X1,X2))
                      | ~ r1_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK8(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,sK9(X0,X1,X7),X7)
                    & r1_lattice3(X0,X1,sK9(X0,X1,X7))
                    & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,X9,sK8(X0,X1))
                  | ~ r1_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK8(X0,X1))
              & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f3025,f3029,f3028,f3027,f3026])).

fof(f3026,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK6(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK6(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3027,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3028,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X8,X7)
                  & r1_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,X6)
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK8(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK8(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3029,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK9(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK9(X0,X1,X7))
        & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X8,X7)
                        & r1_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X9,X6)
                    | ~ r1_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3024])).

fof(f3024,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( X2 = X3
                    | ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_lattice3(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X2)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3007])).

fof(f3007,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3006])).

fof(f3006,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2984])).

fof(f2984,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2966])).

fof(f2966,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f4584,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_49 ),
    inference(avatar_component_clause,[],[f4583])).

fof(f5656,plain,
    ( spl11_31
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(avatar_split_clause,[],[f5655,f4583,f3117,f3113,f3109,f3089,f4404])).

fof(f4404,plain,
    ( spl11_31
  <=> r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f5655,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5654,f3118])).

fof(f5654,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5653,f3114])).

fof(f5653,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5652,f3110])).

fof(f5652,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_49 ),
    inference(subsumption_resolution,[],[f5645,f3090])).

fof(f5645,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_49 ),
    inference(resolution,[],[f4584,f3074])).

fof(f3074,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5622,plain,
    ( ~ spl11_46
    | ~ spl11_45
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47
    | spl11_50 ),
    inference(avatar_split_clause,[],[f5620,f4611,f4569,f3121,f3117,f3113,f3109,f3089,f4553,f4557])).

fof(f4557,plain,
    ( spl11_46
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f3121,plain,
    ( spl11_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f4569,plain,
    ( spl11_47
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f4611,plain,
    ( spl11_50
  <=> sK3 = sK6(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f5620,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47
    | spl11_50 ),
    inference(subsumption_resolution,[],[f5613,f4612])).

fof(f4612,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | spl11_50 ),
    inference(avatar_component_clause,[],[f4611])).

fof(f5613,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5612,f3114])).

fof(f5612,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5607,f3110])).

fof(f5607,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_47 ),
    inference(resolution,[],[f5480,f4427])).

fof(f4427,plain,
    ( ! [X14] :
        ( ~ r1_orders_2(sK0,sK3,X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X14,sK3)
        | sK3 = X14 )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(resolution,[],[f3114,f3216])).

fof(f3216,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | X0 = X1 )
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f3215,f3118])).

fof(f3215,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl11_9 ),
    inference(resolution,[],[f3041,f3122])).

fof(f3122,plain,
    ( v5_orders_2(sK0)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f3121])).

fof(f3041,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f2994])).

fof(f2994,plain,(
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
    inference(flattening,[],[f2993])).

fof(f2993,plain,(
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
    inference(ennf_transformation,[],[f1953])).

fof(f1953,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f5480,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5479,f3090])).

fof(f5479,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | r2_yellow_0(sK0,sK1) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5472,f3110])).

fof(f5472,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ r1_lattice3(sK0,sK1,sK3)
        | r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | r2_yellow_0(sK0,sK1) )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(resolution,[],[f4586,f4441])).

fof(f4441,plain,
    ( ! [X35,X36] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X35,sK3),sK3)
        | ~ m1_subset_1(X36,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X35,X36)
        | ~ r1_lattice3(sK0,X35,sK3)
        | r1_orders_2(sK0,X36,sK6(sK0,X35,sK3))
        | r2_yellow_0(sK0,X35) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3114,f3458])).

fof(f3458,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X1,X2),X2)
        | ~ r1_lattice3(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | r2_yellow_0(sK0,X1) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3079,f3118])).

fof(f3079,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4586,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f4569])).

fof(f5619,plain,
    ( spl11_31
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f5618,f4569,f3117,f3113,f3109,f3089,f4404])).

fof(f5618,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5617,f3090])).

fof(f5617,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5473,f3110])).

fof(f5473,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(resolution,[],[f4586,f4437])).

fof(f4437,plain,
    ( ! [X28] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X28,sK3),sK3)
        | ~ r1_lattice3(sK0,X28,sK3)
        | r1_lattice3(sK0,X28,sK6(sK0,X28,sK3))
        | r2_yellow_0(sK0,X28) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3114,f3388])).

fof(f3388,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1),X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_lattice3(sK0,X0,sK6(sK0,X0,X1))
        | r2_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3076,f3118])).

fof(f3076,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5483,plain,
    ( ~ spl11_50
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(avatar_split_clause,[],[f5482,f4569,f3117,f3113,f3109,f3089,f4611])).

fof(f5482,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5481,f3090])).

fof(f5481,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f5474,f3110])).

fof(f5474,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_47 ),
    inference(resolution,[],[f4586,f4435])).

fof(f4435,plain,
    ( ! [X26] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X26,sK3),sK3)
        | ~ r1_lattice3(sK0,X26,sK3)
        | sK3 != sK6(sK0,X26,sK3)
        | r2_yellow_0(sK0,X26) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3114,f3274])).

fof(f3274,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1),X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | sK6(sK0,X0,X1) != X1
        | r2_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3082,f3118])).

fof(f3082,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sK6(X0,X1,X2) != X2
      | ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5444,plain,
    ( spl11_47
    | ~ spl11_49
    | ~ spl11_5
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f5442,f4407,f3105,f4583,f4569])).

fof(f3105,plain,
    ( spl11_5
  <=> ! [X5] :
        ( r1_orders_2(sK0,X5,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f4407,plain,
    ( spl11_32
  <=> r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f5442,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ spl11_5
    | ~ spl11_32 ),
    inference(resolution,[],[f4408,f3106])).

fof(f3106,plain,
    ( ! [X5] :
        ( ~ r1_lattice3(sK0,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_orders_2(sK0,X5,sK3) )
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f3105])).

fof(f4408,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f4407])).

fof(f5440,plain,
    ( spl11_46
    | ~ spl11_45
    | ~ spl11_5
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f5438,f4404,f3105,f4553,f4557])).

fof(f5438,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | ~ spl11_5
    | ~ spl11_31 ),
    inference(resolution,[],[f4405,f3106])).

fof(f4405,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f4404])).

fof(f5429,plain,
    ( spl11_32
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f5428,f4611,f3117,f3113,f3109,f3089,f4407])).

fof(f5428,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f5427,f3090])).

fof(f5427,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f5426,f3110])).

fof(f5426,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(trivial_inequality_removal,[],[f5423])).

fof(f5423,plain,
    ( sK3 != sK3
    | ~ r1_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_50 ),
    inference(superposition,[],[f4434,f5081])).

fof(f5081,plain,
    ( sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f4611])).

fof(f4434,plain,
    ( ! [X25] :
        ( sK3 != sK6(sK0,X25,sK3)
        | ~ r1_lattice3(sK0,X25,sK3)
        | r1_lattice3(sK0,X25,sK7(sK0,X25,sK3))
        | r2_yellow_0(sK0,X25) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3114,f3272])).

fof(f3272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r1_lattice3(sK0,X0,X1)
        | sK6(sK0,X0,X1) != X1
        | r2_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3081,f3118])).

fof(f3081,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sK6(X0,X1,X2) != X2
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5415,plain,
    ( spl11_50
    | ~ spl11_45
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_46
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f5414,f4626,f4557,f3121,f3117,f3113,f3109,f4553,f4611])).

fof(f4626,plain,
    ( spl11_51
  <=> ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f5414,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_46
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f5413,f4558])).

fof(f4558,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f4557])).

fof(f5413,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f5412,f3110])).

fof(f5412,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_51 ),
    inference(subsumption_resolution,[],[f5382,f3114])).

fof(f5382,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_51 ),
    inference(resolution,[],[f4627,f4427])).

fof(f4627,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0) )
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f4626])).

fof(f5377,plain,
    ( spl11_32
    | spl11_51
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f5376,f3117,f3113,f3109,f3089,f4626,f4407])).

fof(f5376,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X12)
        | r1_orders_2(sK0,X12,sK6(sK0,sK1,sK3)) )
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f5368,f3090])).

fof(f5368,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X12)
        | r1_orders_2(sK0,X12,sK6(sK0,sK1,sK3))
        | r2_yellow_0(sK0,sK1) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f4440,f3110])).

fof(f4440,plain,
    ( ! [X33,X34] :
        ( ~ r1_lattice3(sK0,X33,sK3)
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | r1_lattice3(sK0,X33,sK7(sK0,X33,sK3))
        | ~ r1_lattice3(sK0,X33,X34)
        | r1_orders_2(sK0,X34,sK6(sK0,X33,sK3))
        | r2_yellow_0(sK0,X33) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3114,f3449])).

fof(f3449,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK7(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | r2_yellow_0(sK0,X1) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3078,f3118])).

fof(f3078,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5072,plain,
    ( ~ spl11_53
    | ~ spl11_3
    | ~ spl11_33
    | spl11_85 ),
    inference(avatar_split_clause,[],[f5071,f5067,f4413,f3096,f4641])).

fof(f4641,plain,
    ( spl11_53
  <=> m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f3096,plain,
    ( spl11_3
  <=> ! [X2] :
        ( r1_lattice3(sK0,sK1,sK2(X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f4413,plain,
    ( spl11_33
  <=> r1_lattice3(sK0,sK1,sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f5067,plain,
    ( spl11_85
  <=> r1_lattice3(sK0,sK1,sK2(sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_85])])).

fof(f5071,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_3
    | ~ spl11_33
    | spl11_85 ),
    inference(subsumption_resolution,[],[f5070,f4414])).

fof(f4414,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f4413])).

fof(f5070,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_3
    | spl11_85 ),
    inference(resolution,[],[f5068,f3097])).

fof(f3097,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK2(X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2) )
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f3096])).

fof(f5068,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | spl11_85 ),
    inference(avatar_component_clause,[],[f5067])).

fof(f5069,plain,
    ( ~ spl11_53
    | ~ spl11_85
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_33
    | spl11_52 ),
    inference(avatar_split_clause,[],[f5065,f4638,f4413,f3117,f3100,f3089,f5067,f4641])).

fof(f3100,plain,
    ( spl11_4
  <=> ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f4638,plain,
    ( spl11_52
  <=> r1_orders_2(sK0,sK2(sK8(sK0,sK1)),sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f5065,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_33
    | spl11_52 ),
    inference(subsumption_resolution,[],[f5064,f3103])).

fof(f3103,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f5064,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_33
    | spl11_52 ),
    inference(subsumption_resolution,[],[f5063,f4414])).

fof(f5063,plain,
    ( ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_4
    | ~ spl11_8
    | spl11_52 ),
    inference(resolution,[],[f4639,f4500])).

fof(f4500,plain,
    ( ! [X12,X13] :
        ( r1_orders_2(sK0,sK2(X12),sK8(sK0,X13))
        | ~ r1_lattice3(sK0,sK1,X12)
        | ~ r1_lattice3(sK0,X13,sK2(X12))
        | ~ r2_yellow_0(sK0,X13)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(resolution,[],[f3101,f3174])).

fof(f3174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ r2_yellow_0(sK0,X0)
        | r1_orders_2(sK0,X1,sK8(sK0,X0)) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3067,f3118])).

fof(f3067,plain,(
    ! [X0,X1,X9] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X9,sK8(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f3101,plain,
    ( ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f3100])).

fof(f4639,plain,
    ( ~ r1_orders_2(sK0,sK2(sK8(sK0,sK1)),sK8(sK0,sK1))
    | spl11_52 ),
    inference(avatar_component_clause,[],[f4638])).

fof(f5062,plain,
    ( ~ spl11_52
    | ~ spl11_53
    | ~ spl11_2
    | ~ spl11_33 ),
    inference(avatar_split_clause,[],[f5056,f4413,f3092,f4641,f4638])).

fof(f3092,plain,
    ( spl11_2
  <=> ! [X2] :
        ( ~ r1_orders_2(sK0,sK2(X2),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f5056,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2(sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ spl11_2
    | ~ spl11_33 ),
    inference(resolution,[],[f4414,f3093])).

fof(f3093,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(X2),X2) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f3092])).

fof(f4780,plain,
    ( ~ spl11_1
    | ~ spl11_8
    | spl11_53 ),
    inference(avatar_contradiction_clause,[],[f4779])).

fof(f4779,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_8
    | spl11_53 ),
    inference(subsumption_resolution,[],[f4778,f3118])).

fof(f4778,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_1
    | spl11_53 ),
    inference(subsumption_resolution,[],[f4776,f3103])).

fof(f4776,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | spl11_53 ),
    inference(resolution,[],[f4642,f3065])).

fof(f3065,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4642,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | spl11_53 ),
    inference(avatar_component_clause,[],[f4641])).

fof(f4635,plain,
    ( spl11_33
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f4634,f3117,f3089,f4413])).

fof(f4634,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(resolution,[],[f3103,f3138])).

fof(f3138,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK8(sK0,X0)) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3066,f3118])).

fof(f3066,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK8(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4632,plain,
    ( ~ spl11_47
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_45 ),
    inference(avatar_split_clause,[],[f4631,f4553,f3117,f3113,f3109,f3089,f4569])).

fof(f4631,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4630,f3118])).

fof(f4630,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4629,f3114])).

fof(f4629,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4562,f3110])).

fof(f4562,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3),sK3)
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_45 ),
    inference(resolution,[],[f4554,f3073])).

fof(f3073,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4554,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_45 ),
    inference(avatar_component_clause,[],[f4553])).

fof(f4628,plain,
    ( spl11_1
    | spl11_51
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(avatar_split_clause,[],[f4624,f4583,f3117,f3113,f3109,f4626,f3089])).

fof(f4624,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1) )
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4623,f3118])).

fof(f4623,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_6
    | ~ spl11_7
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4622,f3114])).

fof(f4622,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_6
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4591,f3110])).

fof(f4591,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK1,sK3))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ r1_lattice3(sK0,sK1,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | spl11_49 ),
    inference(resolution,[],[f4584,f3077])).

fof(f3077,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X4,sK6(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4617,plain,
    ( spl11_1
    | ~ spl11_50
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(avatar_split_clause,[],[f4616,f4583,f3117,f3113,f3109,f4611,f3089])).

fof(f4616,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4615,f3118])).

fof(f4615,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4614,f3114])).

fof(f4614,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_6
    | spl11_49 ),
    inference(subsumption_resolution,[],[f4594,f3110])).

fof(f4594,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_49 ),
    inference(resolution,[],[f4584,f3080])).

fof(f3080,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | sK6(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4576,plain,
    ( spl11_32
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_45 ),
    inference(avatar_split_clause,[],[f4575,f4553,f3117,f3113,f3109,f3089,f4407])).

fof(f4575,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4574,f3118])).

fof(f4574,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4573,f3114])).

fof(f4573,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4572,f3110])).

fof(f4572,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_45 ),
    inference(subsumption_resolution,[],[f4563,f3090])).

fof(f4563,plain,
    ( r2_yellow_0(sK0,sK1)
    | r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ r1_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_45 ),
    inference(resolution,[],[f4554,f3072])).

fof(f3072,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4409,plain,
    ( spl11_31
    | spl11_32
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f4402,f3117,f3113,f3109,f3089,f4407,f4404])).

fof(f4402,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f4382,f3090])).

fof(f4382,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r2_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3691,f3110])).

fof(f3691,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK3)
        | r1_lattice3(sK0,X0,sK7(sK0,X0,sK3))
        | r1_lattice3(sK0,X0,sK6(sK0,X0,sK3))
        | r2_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3368,f3114])).

fof(f3368,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_lattice3(sK0,X0,sK6(sK0,X0,X1))
        | r2_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3075,f3118])).

fof(f3075,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f3123,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f3033,f3121])).

fof(f3033,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3016,plain,
    ( ( ! [X2] :
          ( ( ~ r1_orders_2(sK0,sK2(X2),X2)
            & r1_lattice3(sK0,sK1,sK2(X2))
            & m1_subset_1(sK2(X2),u1_struct_0(sK0)) )
          | ~ r1_lattice3(sK0,sK1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      | ~ r2_yellow_0(sK0,sK1) )
    & ( ( ! [X5] :
            ( r1_orders_2(sK0,X5,sK3)
            | ~ r1_lattice3(sK0,sK1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & r1_lattice3(sK0,sK1,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | r2_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3011,f3015,f3014,f3013,f3012])).

fof(f3012,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_yellow_0(X0,X1) )
            & ( ? [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X4)
                      | ~ r1_lattice3(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(sK0,X3,X2)
                    & r1_lattice3(sK0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ r1_lattice3(sK0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r2_yellow_0(sK0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(sK0,X5,X4)
                    | ~ r1_lattice3(sK0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                & r1_lattice3(sK0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | r2_yellow_0(sK0,X1) ) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3013,plain,
    ( ? [X1] :
        ( ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK0,X3,X2)
                  & r1_lattice3(sK0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ r1_lattice3(sK0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ r2_yellow_0(sK0,X1) )
        & ( ? [X4] :
              ( ! [X5] :
                  ( r1_orders_2(sK0,X5,X4)
                  | ~ r1_lattice3(sK0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              & r1_lattice3(sK0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | r2_yellow_0(sK0,X1) ) )
   => ( ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(sK0,X3,X2)
                & r1_lattice3(sK0,sK1,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ r1_lattice3(sK0,sK1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ r2_yellow_0(sK0,sK1) )
      & ( ? [X4] :
            ( ! [X5] :
                ( r1_orders_2(sK0,X5,X4)
                | ~ r1_lattice3(sK0,sK1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            & r1_lattice3(sK0,sK1,X4)
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        | r2_yellow_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3014,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(sK0,X3,X2)
          & r1_lattice3(sK0,sK1,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
     => ( ~ r1_orders_2(sK0,sK2(X2),X2)
        & r1_lattice3(sK0,sK1,sK2(X2))
        & m1_subset_1(sK2(X2),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3015,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( r1_orders_2(sK0,X5,X4)
            | ~ r1_lattice3(sK0,sK1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & r1_lattice3(sK0,sK1,X4)
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ! [X5] :
          ( r1_orders_2(sK0,X5,sK3)
          | ~ r1_lattice3(sK0,sK1,X5)
          | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
      & r1_lattice3(sK0,sK1,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3011,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f3010])).

fof(f3010,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2992])).

fof(f2992,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f2991])).

fof(f2991,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2974])).

fof(f2974,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( r2_yellow_0(X0,X1)
          <=> ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f2973])).

fof(f2973,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f3119,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f3034,f3117])).

fof(f3034,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3115,plain,
    ( spl11_1
    | spl11_7 ),
    inference(avatar_split_clause,[],[f3035,f3113,f3089])).

fof(f3035,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3111,plain,
    ( spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f3036,f3109,f3089])).

fof(f3036,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3107,plain,
    ( spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f3037,f3105,f3089])).

fof(f3037,plain,(
    ! [X5] :
      ( r1_orders_2(sK0,X5,sK3)
      | ~ r1_lattice3(sK0,sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3102,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f3038,f3100,f3089])).

fof(f3038,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3098,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f3039,f3096,f3089])).

fof(f3039,plain,(
    ! [X2] :
      ( r1_lattice3(sK0,sK1,sK2(X2))
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3094,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f3040,f3092,f3089])).

fof(f3040,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,sK2(X2),X2)
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3016])).
%------------------------------------------------------------------------------
