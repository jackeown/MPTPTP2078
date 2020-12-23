%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1537+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 672 expanded)
%              Number of leaves         :   32 ( 315 expanded)
%              Depth                    :   16
%              Number of atoms          : 1150 (5070 expanded)
%              Number of equality atoms :   41 ( 242 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3060,f3064,f3068,f3073,f3077,f3081,f3085,f3089,f3483,f3496,f3535,f3884,f3915,f3916,f3970,f4009,f4025,f4031,f4034,f4066,f4113,f4144,f4149,f4169,f4176,f4200,f4280,f4284])).

fof(f4284,plain,
    ( spl11_18
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(avatar_split_clause,[],[f4283,f4070,f3083,f3079,f3075,f3055,f3480])).

fof(f3480,plain,
    ( spl11_18
  <=> r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f3055,plain,
    ( spl11_1
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f3075,plain,
    ( spl11_6
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f3079,plain,
    ( spl11_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f3083,plain,
    ( spl11_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f4070,plain,
    ( spl11_58
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f4283,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4282,f3056])).

fof(f3056,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f3055])).

fof(f4282,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4281,f3080])).

fof(f3080,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f3079])).

fof(f4281,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4275,f3076])).

fof(f3076,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f4275,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(duplicate_literal_removal,[],[f4272])).

fof(f4272,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(resolution,[],[f4071,f3431])).

fof(f3431,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK6(sK0,X0,X1),sK3)
        | ~ r2_lattice3(sK0,X0,sK3)
        | r2_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3258,f3080])).

fof(f3258,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | r1_orders_2(sK0,sK6(sK0,X0,X1),X2)
        | r2_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3048,f3084])).

fof(f3084,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f3083])).

fof(f3048,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK6(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3016,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK6(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,sK6(X0,X1,X2),X4)
                      | ~ r2_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK8(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,X7,sK9(X0,X1,X7))
                    & r2_lattice3(X0,X1,sK9(X0,X1,X7))
                    & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,sK8(X0,X1),X9)
                  | ~ r2_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK8(X0,X1))
              & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f3011,f3015,f3014,f3013,f3012])).

fof(f3012,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X3,X4)
              | ~ r2_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK6(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,sK6(X0,X1,X2),X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3013,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X5)
          & r2_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3014,plain,(
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
            ( sK8(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X7,X8)
                & r2_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,sK8(X0,X1),X9)
            | ~ r2_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3015,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X7,X8)
          & r2_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X7,sK9(X0,X1,X7))
        & r2_lattice3(X0,X1,sK9(X0,X1,X7))
        & m1_subset_1(sK9(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3011,plain,(
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
    inference(rectify,[],[f3010])).

fof(f3010,plain,(
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
    inference(nnf_transformation,[],[f2995])).

fof(f2995,plain,(
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
    inference(flattening,[],[f2994])).

fof(f2994,plain,(
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
    inference(ennf_transformation,[],[f2983])).

fof(f2983,plain,(
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
    inference(rectify,[],[f2965])).

fof(f2965,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f4071,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | spl11_58 ),
    inference(avatar_component_clause,[],[f4070])).

fof(f4280,plain,
    ( ~ spl11_49
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(avatar_split_clause,[],[f4279,f4070,f3083,f3079,f3075,f3055,f3965])).

fof(f3965,plain,
    ( spl11_49
  <=> r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f4279,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4278,f3056])).

fof(f4278,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4277,f3080])).

fof(f4277,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(subsumption_resolution,[],[f4276,f3076])).

fof(f4276,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(duplicate_literal_removal,[],[f4271])).

fof(f4271,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | spl11_58 ),
    inference(resolution,[],[f4071,f3453])).

fof(f3453,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK6(sK0,X0,X1),sK3)
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3268,f3080])).

fof(f3268,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X2)
        | r1_orders_2(sK0,sK6(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3049,f3084])).

fof(f3049,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK6(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4200,plain,
    ( ~ spl11_58
    | ~ spl11_52
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_53
    | ~ spl11_56 ),
    inference(avatar_split_clause,[],[f4199,f4046,f4023,f3087,f3083,f3079,f4015,f4070])).

fof(f4015,plain,
    ( spl11_52
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f3087,plain,
    ( spl11_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f4023,plain,
    ( spl11_53
  <=> sK3 = sK6(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f4046,plain,
    ( spl11_56
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f4199,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | spl11_53
    | ~ spl11_56 ),
    inference(subsumption_resolution,[],[f4198,f4024])).

fof(f4024,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | spl11_53 ),
    inference(avatar_component_clause,[],[f4023])).

fof(f4198,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK3)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9
    | ~ spl11_56 ),
    inference(resolution,[],[f4047,f3216])).

fof(f3216,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | sK3 = X0 )
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(resolution,[],[f3135,f3080])).

fof(f3135,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | X0 = X1 )
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f3134,f3084])).

fof(f3134,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl11_9 ),
    inference(resolution,[],[f3027,f3088])).

fof(f3088,plain,
    ( v5_orders_2(sK0)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f3087])).

fof(f3027,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f2990])).

fof(f2990,plain,(
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
    inference(flattening,[],[f2989])).

fof(f2989,plain,(
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

fof(f4047,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f4046])).

fof(f4176,plain,
    ( spl11_56
    | ~ spl11_52
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f4174,f3477,f3071,f4015,f4046])).

fof(f3071,plain,
    ( spl11_5
  <=> ! [X5] :
        ( r1_orders_2(sK0,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f3477,plain,
    ( spl11_17
  <=> r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f4174,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK3))
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(resolution,[],[f3478,f3072])).

fof(f3072,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK0,sK1,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X5) )
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f3071])).

fof(f3478,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f3477])).

fof(f4169,plain,
    ( spl11_18
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(avatar_split_clause,[],[f4168,f4023,f3083,f3079,f3075,f3055,f3480])).

fof(f4168,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f4167,f3056])).

fof(f4167,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(subsumption_resolution,[],[f4162,f3076])).

fof(f4162,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(trivial_inequality_removal,[],[f4155])).

fof(f4155,plain,
    ( sK3 != sK3
    | ~ r2_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_53 ),
    inference(superposition,[],[f3311,f4150])).

fof(f4150,plain,
    ( sK3 = sK6(sK0,sK1,sK3)
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f4023])).

fof(f3311,plain,
    ( ! [X0] :
        ( sK3 != sK6(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,X0,sK3)
        | r2_lattice3(sK0,X0,sK7(sK0,X0,sK3))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3158,f3080])).

fof(f3158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | sK6(sK0,X0,X1) != X1
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3051,f3084])).

fof(f3051,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sK6(X0,X1,X2) != X2
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4149,plain,
    ( ~ spl11_49
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_52 ),
    inference(avatar_split_clause,[],[f4147,f4015,f3083,f3079,f3075,f3055,f3965])).

fof(f4147,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4146,f3084])).

fof(f4146,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4145,f3080])).

fof(f4145,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4134,f3076])).

fof(f4134,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4131,f3056])).

fof(f4131,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_52 ),
    inference(resolution,[],[f4048,f3043])).

fof(f3043,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4048,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_52 ),
    inference(avatar_component_clause,[],[f4015])).

fof(f4144,plain,
    ( spl11_18
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_52 ),
    inference(avatar_split_clause,[],[f4143,f4015,f3083,f3079,f3075,f3055,f3480])).

fof(f4143,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4142,f3084])).

fof(f4142,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4141,f3080])).

fof(f4141,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4140,f3076])).

fof(f4140,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_52 ),
    inference(subsumption_resolution,[],[f4132,f3056])).

fof(f4132,plain,
    ( r1_yellow_0(sK0,sK1)
    | r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_52 ),
    inference(resolution,[],[f4048,f3042])).

fof(f3042,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4113,plain,
    ( spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50
    | spl11_58 ),
    inference(avatar_contradiction_clause,[],[f4110])).

fof(f4110,plain,
    ( $false
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50
    | spl11_58 ),
    inference(unit_resulting_resolution,[],[f3084,f3056,f3080,f3076,f3080,f3076,f3969,f4071,f3047])).

fof(f3047,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,sK6(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3969,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_50 ),
    inference(avatar_component_clause,[],[f3968])).

fof(f3968,plain,
    ( spl11_50
  <=> m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f4066,plain,
    ( spl11_52
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(avatar_split_clause,[],[f4065,f3968,f3083,f3079,f3075,f3055,f4015])).

fof(f4065,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4064,f3084])).

fof(f4064,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4063,f3080])).

fof(f4063,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4062,f3076])).

fof(f4062,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4056,f3056])).

fof(f4056,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_50 ),
    inference(resolution,[],[f3969,f3041])).

fof(f3041,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4034,plain,
    ( ~ spl11_53
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f4033,f3965,f3083,f3079,f3075,f3055,f4023])).

fof(f4033,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f4032,f3056])).

fof(f4032,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f4027,f3076])).

fof(f4027,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | sK3 != sK6(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(resolution,[],[f3966,f3333])).

fof(f3333,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3,sK7(sK0,X0,sK3))
        | ~ r2_lattice3(sK0,X0,sK3)
        | sK3 != sK6(sK0,X0,sK3)
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3160,f3080])).

fof(f3160,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | sK6(sK0,X0,X1) != X1
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3052,f3084])).

fof(f3052,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sK6(X0,X1,X2) != X2
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3966,plain,
    ( r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f3965])).

fof(f4031,plain,
    ( spl11_17
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(avatar_split_clause,[],[f4030,f3965,f3083,f3079,f3075,f3055,f3477])).

fof(f4030,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f4029,f3056])).

fof(f4029,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(subsumption_resolution,[],[f4026,f3076])).

fof(f4026,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_49 ),
    inference(resolution,[],[f3966,f3373])).

fof(f3373,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3,sK7(sK0,X0,sK3))
        | ~ r2_lattice3(sK0,X0,sK3)
        | r2_lattice3(sK0,X0,sK6(sK0,X0,sK3))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3214,f3080])).

fof(f3214,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | r2_lattice3(sK0,X0,sK6(sK0,X0,X1))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3046,f3084])).

fof(f3046,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4025,plain,
    ( ~ spl11_53
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(avatar_split_clause,[],[f4021,f3968,f3083,f3079,f3075,f3055,f4023])).

fof(f4021,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4020,f3084])).

fof(f4020,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4019,f3080])).

fof(f4019,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4018,f3076])).

fof(f4018,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4000,f3056])).

fof(f4000,plain,
    ( sK3 != sK6(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_50 ),
    inference(resolution,[],[f3969,f3050])).

fof(f3050,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | sK6(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f4009,plain,
    ( spl11_17
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(avatar_split_clause,[],[f4008,f3968,f3083,f3079,f3075,f3055,f3477])).

fof(f4008,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4007,f3084])).

fof(f4007,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_7
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4006,f3080])).

fof(f4006,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | ~ spl11_6
    | spl11_50 ),
    inference(subsumption_resolution,[],[f4005,f3076])).

fof(f4005,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_1
    | spl11_50 ),
    inference(subsumption_resolution,[],[f3998,f3056])).

fof(f3998,plain,
    ( r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ r2_lattice3(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl11_50 ),
    inference(resolution,[],[f3969,f3044])).

fof(f3044,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK6(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3970,plain,
    ( spl11_49
    | ~ spl11_50
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f3962,f3480,f3071,f3968,f3965])).

fof(f3962,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK7(sK0,sK1,sK3))
    | ~ spl11_5
    | ~ spl11_18 ),
    inference(resolution,[],[f3481,f3072])).

fof(f3481,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f3480])).

fof(f3916,plain,
    ( ~ spl11_23
    | ~ spl11_1
    | ~ spl11_44
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_21
    | spl11_27 ),
    inference(avatar_split_clause,[],[f3886,f3525,f3494,f3083,f3066,f3889,f3055,f3502])).

fof(f3502,plain,
    ( spl11_23
  <=> m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f3889,plain,
    ( spl11_44
  <=> r2_lattice3(sK0,sK1,sK2(sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f3066,plain,
    ( spl11_4
  <=> ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f3494,plain,
    ( spl11_21
  <=> r2_lattice3(sK0,sK1,sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f3525,plain,
    ( spl11_27
  <=> r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f3886,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_21
    | spl11_27 ),
    inference(subsumption_resolution,[],[f3885,f3495])).

fof(f3495,plain,
    ( r2_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f3494])).

fof(f3885,plain,
    ( ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ r2_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_4
    | ~ spl11_8
    | spl11_27 ),
    inference(resolution,[],[f3526,f3538])).

fof(f3538,plain,
    ( ! [X4,X5] :
        ( r1_orders_2(sK0,sK8(sK0,X5),sK2(X4))
        | ~ r2_lattice3(sK0,sK1,X4)
        | ~ r2_lattice3(sK0,X5,sK2(X4))
        | ~ r1_yellow_0(sK0,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(resolution,[],[f3067,f3113])).

fof(f3113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,sK8(sK0,X0),X1) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3037,f3084])).

fof(f3037,plain,(
    ! [X0,X1,X9] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,sK8(X0,X1),X9) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3067,plain,
    ( ! [X2] :
        ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2) )
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f3066])).

fof(f3526,plain,
    ( ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK8(sK0,sK1)))
    | spl11_27 ),
    inference(avatar_component_clause,[],[f3525])).

fof(f3915,plain,
    ( ~ spl11_23
    | ~ spl11_3
    | ~ spl11_21
    | spl11_44 ),
    inference(avatar_split_clause,[],[f3914,f3889,f3494,f3062,f3502])).

fof(f3062,plain,
    ( spl11_3
  <=> ! [X2] :
        ( r2_lattice3(sK0,sK1,sK2(X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f3914,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl11_3
    | ~ spl11_21
    | spl11_44 ),
    inference(subsumption_resolution,[],[f3913,f3495])).

fof(f3913,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_3
    | spl11_44 ),
    inference(resolution,[],[f3890,f3063])).

fof(f3063,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK1,sK2(X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2) )
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f3062])).

fof(f3890,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK8(sK0,sK1)))
    | spl11_44 ),
    inference(avatar_component_clause,[],[f3889])).

fof(f3884,plain,
    ( ~ spl11_27
    | ~ spl11_23
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(avatar_split_clause,[],[f3882,f3494,f3058,f3502,f3525])).

fof(f3058,plain,
    ( spl11_2
  <=> ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK2(X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f3882,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK8(sK0,sK1)))
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(resolution,[],[f3495,f3059])).

fof(f3059,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2(X2)) )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f3058])).

fof(f3535,plain,
    ( ~ spl11_1
    | ~ spl11_8
    | spl11_23 ),
    inference(avatar_contradiction_clause,[],[f3534])).

fof(f3534,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_8
    | spl11_23 ),
    inference(subsumption_resolution,[],[f3533,f3084])).

fof(f3533,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_1
    | spl11_23 ),
    inference(subsumption_resolution,[],[f3531,f3069])).

fof(f3069,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f3055])).

fof(f3531,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | spl11_23 ),
    inference(resolution,[],[f3503,f3035])).

fof(f3035,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3503,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | spl11_23 ),
    inference(avatar_component_clause,[],[f3502])).

fof(f3496,plain,
    ( spl11_21
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f3492,f3083,f3055,f3494])).

fof(f3492,plain,
    ( r2_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl11_1
    | ~ spl11_8 ),
    inference(resolution,[],[f3069,f3100])).

fof(f3100,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | r2_lattice3(sK0,X0,sK8(sK0,X0)) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3036,f3084])).

fof(f3036,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK8(X0,X1)) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3483,plain,
    ( spl11_1
    | spl11_17
    | spl11_18
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f3473,f3083,f3079,f3075,f3480,f3477,f3055])).

fof(f3473,plain,
    ( r2_lattice3(sK0,sK1,sK7(sK0,sK1,sK3))
    | r2_lattice3(sK0,sK1,sK6(sK0,sK1,sK3))
    | r1_yellow_0(sK0,sK1)
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3353,f3076])).

fof(f3353,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK3)
        | r2_lattice3(sK0,X0,sK7(sK0,X0,sK3))
        | r2_lattice3(sK0,X0,sK6(sK0,X0,sK3))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(resolution,[],[f3212,f3080])).

fof(f3212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK7(sK0,X0,X1))
        | ~ r2_lattice3(sK0,X0,X1)
        | r2_lattice3(sK0,X0,sK6(sK0,X0,X1))
        | r1_yellow_0(sK0,X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f3045,f3084])).

fof(f3045,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK6(X0,X1,X2))
      | r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3089,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f3019,f3087])).

fof(f3019,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3002,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2997,f3001,f3000,f2999,f2998])).

fof(f2998,plain,
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

fof(f2999,plain,
    ( ? [X1] :
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
   => ( ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(sK0,X2,X3)
                & r2_lattice3(sK0,sK1,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ r2_lattice3(sK0,sK1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ r1_yellow_0(sK0,sK1) )
      & ( ? [X4] :
            ( ! [X5] :
                ( r1_orders_2(sK0,X4,X5)
                | ~ r2_lattice3(sK0,sK1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            & r2_lattice3(sK0,sK1,X4)
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        | r1_yellow_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3000,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(sK0,X2,X3)
          & r2_lattice3(sK0,sK1,X3)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
     => ( ~ r1_orders_2(sK0,X2,sK2(X2))
        & r2_lattice3(sK0,sK1,sK2(X2))
        & m1_subset_1(sK2(X2),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3001,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( r1_orders_2(sK0,X4,X5)
            | ~ r2_lattice3(sK0,sK1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK1,X4)
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ! [X5] :
          ( r1_orders_2(sK0,sK3,X5)
          | ~ r2_lattice3(sK0,sK1,X5)
          | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
      & r2_lattice3(sK0,sK1,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2997,plain,(
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
    inference(rectify,[],[f2996])).

fof(f2996,plain,(
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
    inference(nnf_transformation,[],[f2988])).

fof(f2988,plain,(
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
    inference(flattening,[],[f2987])).

fof(f2987,plain,(
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
    inference(ennf_transformation,[],[f2973])).

fof(f2973,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2972])).

fof(f2972,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f3085,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f3020,f3083])).

fof(f3020,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3081,plain,
    ( spl11_1
    | spl11_7 ),
    inference(avatar_split_clause,[],[f3021,f3079,f3055])).

fof(f3021,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3077,plain,
    ( spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f3022,f3075,f3055])).

fof(f3022,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3073,plain,
    ( spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f3023,f3071,f3055])).

fof(f3023,plain,(
    ! [X5] :
      ( r1_orders_2(sK0,sK3,X5)
      | ~ r2_lattice3(sK0,sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3068,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f3024,f3066,f3055])).

fof(f3024,plain,(
    ! [X2] :
      ( m1_subset_1(sK2(X2),u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3064,plain,
    ( ~ spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f3025,f3062,f3055])).

fof(f3025,plain,(
    ! [X2] :
      ( r2_lattice3(sK0,sK1,sK2(X2))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3002])).

fof(f3060,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f3026,f3058,f3055])).

fof(f3026,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,X2,sK2(X2))
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f3002])).
%------------------------------------------------------------------------------
