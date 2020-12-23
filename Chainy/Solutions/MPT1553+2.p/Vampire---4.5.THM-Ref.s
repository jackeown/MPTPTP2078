%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1553+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 957 expanded)
%              Number of leaves         :   33 ( 411 expanded)
%              Depth                    :   20
%              Number of atoms          : 1259 (10595 expanded)
%              Number of equality atoms :   83 (1243 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3361,f3366,f3371,f3375,f3376,f3377,f3378,f3379,f3380,f3381,f3504,f3527,f3537,f3539,f3544,f3546,f3637,f3647,f4151,f4169,f4251,f4321,f4360,f4413,f4482,f4569,f4604,f4628,f4981,f5052,f5253])).

fof(f5253,plain,
    ( ~ spl34_1
    | spl34_16
    | ~ spl34_53
    | ~ spl34_73 ),
    inference(avatar_contradiction_clause,[],[f5252])).

fof(f5252,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f5038,f4189])).

fof(f4189,plain,
    ( r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ spl34_53 ),
    inference(avatar_component_clause,[],[f4187])).

fof(f4187,plain,
    ( spl34_53
  <=> r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_53])])).

fof(f5038,plain,
    ( ~ r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ spl34_1
    | spl34_16
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f5037,f3182])).

fof(f3182,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3107,plain,
    ( ( ( ( ~ r2_yellow_0(sK2,sK4)
          | sK3 != k2_yellow_0(sK2,sK4) )
        & ! [X3] :
            ( r1_orders_2(sK2,X3,sK3)
            | ~ r1_lattice3(sK2,sK4,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
        & r1_lattice3(sK2,sK4,sK3) )
      | ( ( ( ~ r1_orders_2(sK2,sK5,sK3)
            & r1_lattice3(sK2,sK4,sK5)
            & m1_subset_1(sK5,u1_struct_0(sK2)) )
          | ~ r1_lattice3(sK2,sK4,sK3) )
        & r2_yellow_0(sK2,sK4)
        & sK3 = k2_yellow_0(sK2,sK4) ) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f3035,f3106,f3105,f3104,f3103])).

fof(f3103,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r2_yellow_0(X0,X2)
                    | k2_yellow_0(X0,X2) != X1 )
                  & ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X1)
                        & r1_lattice3(X0,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X2,X1) )
                  & r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_yellow_0(sK2,X2)
                  | k2_yellow_0(sK2,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(sK2,X3,X1)
                    | ~ r1_lattice3(sK2,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
                & r1_lattice3(sK2,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(sK2,X4,X1)
                      & r1_lattice3(sK2,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(sK2)) )
                  | ~ r1_lattice3(sK2,X2,X1) )
                & r2_yellow_0(sK2,X2)
                & k2_yellow_0(sK2,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3104,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r2_yellow_0(sK2,X2)
                | k2_yellow_0(sK2,X2) != X1 )
              & ! [X3] :
                  ( r1_orders_2(sK2,X3,X1)
                  | ~ r1_lattice3(sK2,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
              & r1_lattice3(sK2,X2,X1) )
            | ( ( ? [X4] :
                    ( ~ r1_orders_2(sK2,X4,X1)
                    & r1_lattice3(sK2,X2,X4)
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                | ~ r1_lattice3(sK2,X2,X1) )
              & r2_yellow_0(sK2,X2)
              & k2_yellow_0(sK2,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ( ( ~ r2_yellow_0(sK2,X2)
              | k2_yellow_0(sK2,X2) != sK3 )
            & ! [X3] :
                ( r1_orders_2(sK2,X3,sK3)
                | ~ r1_lattice3(sK2,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
            & r1_lattice3(sK2,X2,sK3) )
          | ( ( ? [X4] :
                  ( ~ r1_orders_2(sK2,X4,sK3)
                  & r1_lattice3(sK2,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(sK2)) )
              | ~ r1_lattice3(sK2,X2,sK3) )
            & r2_yellow_0(sK2,X2)
            & k2_yellow_0(sK2,X2) = sK3 ) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3105,plain,
    ( ? [X2] :
        ( ( ( ~ r2_yellow_0(sK2,X2)
            | k2_yellow_0(sK2,X2) != sK3 )
          & ! [X3] :
              ( r1_orders_2(sK2,X3,sK3)
              | ~ r1_lattice3(sK2,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
          & r1_lattice3(sK2,X2,sK3) )
        | ( ( ? [X4] :
                ( ~ r1_orders_2(sK2,X4,sK3)
                & r1_lattice3(sK2,X2,X4)
                & m1_subset_1(X4,u1_struct_0(sK2)) )
            | ~ r1_lattice3(sK2,X2,sK3) )
          & r2_yellow_0(sK2,X2)
          & k2_yellow_0(sK2,X2) = sK3 ) )
   => ( ( ( ~ r2_yellow_0(sK2,sK4)
          | sK3 != k2_yellow_0(sK2,sK4) )
        & ! [X3] :
            ( r1_orders_2(sK2,X3,sK3)
            | ~ r1_lattice3(sK2,sK4,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK2)) )
        & r1_lattice3(sK2,sK4,sK3) )
      | ( ( ? [X4] :
              ( ~ r1_orders_2(sK2,X4,sK3)
              & r1_lattice3(sK2,sK4,X4)
              & m1_subset_1(X4,u1_struct_0(sK2)) )
          | ~ r1_lattice3(sK2,sK4,sK3) )
        & r2_yellow_0(sK2,sK4)
        & sK3 = k2_yellow_0(sK2,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f3106,plain,
    ( ? [X4] :
        ( ~ r1_orders_2(sK2,X4,sK3)
        & r1_lattice3(sK2,sK4,X4)
        & m1_subset_1(X4,u1_struct_0(sK2)) )
   => ( ~ r1_orders_2(sK2,sK5,sK3)
      & r1_lattice3(sK2,sK4,sK5)
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3035,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_yellow_0(X0,X2)
                  | k2_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X1)
                      & r1_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1) )
                & r2_yellow_0(X0,X2)
                & k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f3034])).

fof(f3034,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_yellow_0(X0,X2)
                  | k2_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X1)
                      & r1_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1) )
                & r2_yellow_0(X0,X2)
                & k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3016])).

fof(f3016,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) )
                 => ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 ) )
                & ( ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 )
                 => ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X4)
                         => r1_orders_2(X0,X4,X1) ) )
                    & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f3008])).

fof(f3008,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) )
                 => ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 ) )
                & ( ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 )
                 => ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3007])).

fof(f3007,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f5037,plain,
    ( ~ r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f5036,f3347])).

fof(f3347,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | ~ spl34_1 ),
    inference(avatar_component_clause,[],[f3346])).

fof(f3346,plain,
    ( spl34_1
  <=> r1_lattice3(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_1])])).

fof(f5036,plain,
    ( ~ r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f5019,f3517])).

fof(f3517,plain,
    ( ~ sP0(sK2,sK4)
    | spl34_16 ),
    inference(avatar_component_clause,[],[f3516])).

fof(f3516,plain,
    ( spl34_16
  <=> sP0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_16])])).

fof(f5019,plain,
    ( sP0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_73 ),
    inference(trivial_inequality_removal,[],[f5018])).

fof(f5018,plain,
    ( sK3 != sK3
    | sP0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_73 ),
    inference(superposition,[],[f3279,f4377])).

fof(f4377,plain,
    ( sK3 = sK19(sK2,sK4,sK3)
    | ~ spl34_73 ),
    inference(avatar_component_clause,[],[f4375])).

fof(f4375,plain,
    ( spl34_73
  <=> sK3 = sK19(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_73])])).

fof(f3279,plain,(
    ! [X2,X0,X1] :
      ( sK19(X0,X1,X2) != X2
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3150,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ( sK19(X0,X1,X2) != X2
              & ! [X4] :
                  ( r1_orders_2(X0,X4,sK19(X0,X1,X2))
                  | ~ r1_lattice3(X0,X1,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK19(X0,X1,X2))
              & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X0)) )
            | ( ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
              & r1_lattice3(X0,X1,sK20(X0,X1,X2))
              & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( ! [X7] :
              ( sK21(X0,X1) = X7
              | ( ~ r1_orders_2(X0,sK22(X0,X1,X7),X7)
                & r1_lattice3(X0,X1,sK22(X0,X1,X7))
                & m1_subset_1(sK22(X0,X1,X7),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,sK21(X0,X1))
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,sK21(X0,X1))
          & m1_subset_1(sK21(X0,X1),u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21,sK22])],[f3145,f3149,f3148,f3147,f3146])).

fof(f3146,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK19(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK19(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK19(X0,X1,X2))
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3147,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK20(X0,X1,X2))
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3148,plain,(
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
            ( sK21(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK21(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK21(X0,X1))
        & m1_subset_1(sK21(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3149,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK22(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK22(X0,X1,X7))
        & m1_subset_1(sK22(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3145,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f3144])).

fof(f3144,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3100])).

fof(f3100,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
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
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f5052,plain,
    ( spl34_53
    | ~ spl34_19
    | ~ spl34_7
    | ~ spl34_17 ),
    inference(avatar_split_clause,[],[f5046,f3520,f3373,f3530,f4187])).

fof(f3530,plain,
    ( spl34_19
  <=> m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_19])])).

fof(f3373,plain,
    ( spl34_7
  <=> ! [X3] :
        ( r1_orders_2(sK2,X3,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_7])])).

fof(f3520,plain,
    ( spl34_17
  <=> r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_17])])).

fof(f5046,plain,
    ( ~ m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK20(sK2,sK4,sK3),sK3)
    | ~ spl34_7
    | ~ spl34_17 ),
    inference(resolution,[],[f3522,f3374])).

fof(f3374,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK2,sK4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_orders_2(sK2,X3,sK3) )
    | ~ spl34_7 ),
    inference(avatar_component_clause,[],[f3373])).

fof(f3522,plain,
    ( r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | ~ spl34_17 ),
    inference(avatar_component_clause,[],[f3520])).

fof(f4981,plain,
    ( ~ spl34_1
    | spl34_16
    | ~ spl34_53
    | spl34_74 ),
    inference(avatar_contradiction_clause,[],[f4980])).

fof(f4980,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53
    | spl34_74 ),
    inference(subsumption_resolution,[],[f4979,f3182])).

fof(f4979,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53
    | spl34_74 ),
    inference(subsumption_resolution,[],[f4974,f4384])).

fof(f4384,plain,
    ( ~ r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | spl34_74 ),
    inference(avatar_component_clause,[],[f4382])).

fof(f4382,plain,
    ( spl34_74
  <=> r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_74])])).

fof(f4974,plain,
    ( r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53 ),
    inference(resolution,[],[f4620,f3347])).

fof(f4620,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4619,f3182])).

fof(f4619,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(sK3,u1_struct_0(sK2)) )
    | ~ spl34_1
    | spl34_16
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4618,f3347])).

fof(f4618,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2)) )
    | spl34_16
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4611,f3517])).

fof(f4611,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(sK2,sK4)
        | ~ r1_lattice3(sK2,sK4,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2)) )
    | ~ spl34_53 ),
    inference(resolution,[],[f4189,f3276])).

fof(f3276,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
      | r1_orders_2(X0,X4,sK19(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f4628,plain,
    ( spl34_73
    | ~ spl34_74
    | ~ spl34_18
    | ~ spl34_60 ),
    inference(avatar_split_clause,[],[f4627,f4248,f3524,f4382,f4375])).

fof(f3524,plain,
    ( spl34_18
  <=> m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_18])])).

fof(f4248,plain,
    ( spl34_60
  <=> r1_orders_2(sK2,sK19(sK2,sK4,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_60])])).

fof(f4627,plain,
    ( ~ r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | sK3 = sK19(sK2,sK4,sK3)
    | ~ spl34_18
    | ~ spl34_60 ),
    inference(subsumption_resolution,[],[f4626,f3182])).

fof(f4626,plain,
    ( ~ r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = sK19(sK2,sK4,sK3)
    | ~ spl34_18
    | ~ spl34_60 ),
    inference(subsumption_resolution,[],[f4622,f3526])).

fof(f3526,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ spl34_18 ),
    inference(avatar_component_clause,[],[f3524])).

fof(f4622,plain,
    ( ~ r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | ~ m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = sK19(sK2,sK4,sK3)
    | ~ spl34_60 ),
    inference(resolution,[],[f4250,f3395])).

fof(f3395,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ r1_orders_2(sK2,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | X2 = X3 ) ),
    inference(global_subsumption,[],[f3181,f3383])).

fof(f3383,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ r1_orders_2(sK2,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | X2 = X3 ) ),
    inference(resolution,[],[f3180,f3199])).

fof(f3199,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f3039])).

fof(f3039,plain,(
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
    inference(flattening,[],[f3038])).

fof(f3038,plain,(
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

fof(f3180,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3181,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3107])).

fof(f4250,plain,
    ( r1_orders_2(sK2,sK19(sK2,sK4,sK3),sK3)
    | ~ spl34_60 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f4604,plain,
    ( ~ spl34_1
    | spl34_16
    | spl34_19
    | ~ spl34_73 ),
    inference(avatar_contradiction_clause,[],[f4603])).

fof(f4603,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | spl34_19
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f4377,f4239])).

fof(f4239,plain,
    ( sK3 != sK19(sK2,sK4,sK3)
    | ~ spl34_1
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4238,f3182])).

fof(f4238,plain,
    ( sK3 != sK19(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4237,f3347])).

fof(f4237,plain,
    ( sK3 != sK19(sK2,sK4,sK3)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4233,f3517])).

fof(f4233,plain,
    ( sK3 != sK19(sK2,sK4,sK3)
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_19 ),
    inference(resolution,[],[f3531,f3277])).

fof(f3277,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0))
      | sK19(X0,X1,X2) != X2
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3531,plain,
    ( ~ m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl34_19 ),
    inference(avatar_component_clause,[],[f3530])).

fof(f4569,plain,
    ( ~ spl34_1
    | spl34_16
    | spl34_20
    | ~ spl34_53 ),
    inference(avatar_contradiction_clause,[],[f4568])).

fof(f4568,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | spl34_20
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4567,f3182])).

fof(f4567,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_20
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4566,f3347])).

fof(f4566,plain,
    ( ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | spl34_20
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4565,f3517])).

fof(f4565,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_20
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4557,f3535])).

fof(f3535,plain,
    ( ~ r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | spl34_20 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f3534,plain,
    ( spl34_20
  <=> r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_20])])).

fof(f4557,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_53 ),
    inference(resolution,[],[f4189,f3273])).

fof(f3273,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK19(X0,X1,X2))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f4482,plain,
    ( ~ spl34_1
    | ~ spl34_21
    | spl34_74 ),
    inference(avatar_contradiction_clause,[],[f4481])).

fof(f4481,plain,
    ( $false
    | ~ spl34_1
    | ~ spl34_21
    | spl34_74 ),
    inference(subsumption_resolution,[],[f4384,f4298])).

fof(f4298,plain,
    ( r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | ~ spl34_1
    | ~ spl34_21 ),
    inference(subsumption_resolution,[],[f4294,f3182])).

fof(f4294,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK19(sK2,sK4,sK3))
    | ~ spl34_1
    | ~ spl34_21 ),
    inference(resolution,[],[f3543,f3347])).

fof(f3543,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3)) )
    | ~ spl34_21 ),
    inference(avatar_component_clause,[],[f3542])).

fof(f3542,plain,
    ( spl34_21
  <=> ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_21])])).

fof(f4413,plain,
    ( ~ spl34_1
    | spl34_16
    | spl34_17
    | ~ spl34_73 ),
    inference(avatar_contradiction_clause,[],[f4412])).

fof(f4412,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | spl34_17
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f4411,f3182])).

fof(f4411,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_17
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f4410,f3347])).

fof(f4410,plain,
    ( ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | spl34_17
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f4409,f3521])).

fof(f3521,plain,
    ( ~ r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | spl34_17 ),
    inference(avatar_component_clause,[],[f3520])).

fof(f4409,plain,
    ( r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | ~ spl34_73 ),
    inference(subsumption_resolution,[],[f4408,f3517])).

fof(f4408,plain,
    ( sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_73 ),
    inference(trivial_inequality_removal,[],[f4405])).

fof(f4405,plain,
    ( sK3 != sK3
    | sP0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_73 ),
    inference(superposition,[],[f3278,f4377])).

fof(f3278,plain,(
    ! [X2,X0,X1] :
      ( sK19(X0,X1,X2) != X2
      | sP0(X0,X1)
      | r1_lattice3(X0,X1,sK20(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f4360,plain,
    ( ~ spl34_1
    | spl34_16
    | spl34_18
    | ~ spl34_53 ),
    inference(avatar_contradiction_clause,[],[f4359])).

fof(f4359,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | spl34_18
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4358,f3182])).

fof(f4358,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_18
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4357,f3347])).

fof(f4357,plain,
    ( ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | spl34_18
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4356,f3517])).

fof(f4356,plain,
    ( sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_18
    | ~ spl34_53 ),
    inference(subsumption_resolution,[],[f4335,f3525])).

fof(f3525,plain,
    ( ~ m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | spl34_18 ),
    inference(avatar_component_clause,[],[f3524])).

fof(f4335,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_53 ),
    inference(resolution,[],[f4189,f3270])).

fof(f3270,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK20(X0,X1,X2),X2)
      | m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f4321,plain,
    ( ~ spl34_1
    | spl34_16
    | spl34_18
    | spl34_19 ),
    inference(avatar_contradiction_clause,[],[f4320])).

fof(f4320,plain,
    ( $false
    | ~ spl34_1
    | spl34_16
    | spl34_18
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4236,f3525])).

fof(f4236,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4235,f3182])).

fof(f4235,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4234,f3347])).

fof(f4234,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_16
    | spl34_19 ),
    inference(subsumption_resolution,[],[f4232,f3517])).

fof(f4232,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ r1_lattice3(sK2,sK4,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl34_19 ),
    inference(resolution,[],[f3531,f3268])).

fof(f3268,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f4251,plain,
    ( spl34_60
    | ~ spl34_18
    | ~ spl34_7
    | ~ spl34_20 ),
    inference(avatar_split_clause,[],[f4241,f3534,f3373,f3524,f4248])).

fof(f4241,plain,
    ( ~ m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK19(sK2,sK4,sK3),sK3)
    | ~ spl34_7
    | ~ spl34_20 ),
    inference(resolution,[],[f3536,f3374])).

fof(f3536,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | ~ spl34_20 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f4169,plain,
    ( spl34_4
    | ~ spl34_16 ),
    inference(avatar_contradiction_clause,[],[f4168])).

fof(f4168,plain,
    ( $false
    | spl34_4
    | ~ spl34_16 ),
    inference(subsumption_resolution,[],[f3562,f3360])).

fof(f3360,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | spl34_4 ),
    inference(avatar_component_clause,[],[f3358])).

fof(f3358,plain,
    ( spl34_4
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_4])])).

fof(f3562,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl34_16 ),
    inference(resolution,[],[f3482,f3518])).

fof(f3518,plain,
    ( sP0(sK2,sK4)
    | ~ spl34_16 ),
    inference(avatar_component_clause,[],[f3516])).

fof(f3482,plain,(
    ! [X1] :
      ( ~ sP0(sK2,X1)
      | r2_yellow_0(sK2,X1) ) ),
    inference(resolution,[],[f3437,f3261])).

fof(f3261,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3143])).

fof(f3143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f3101])).

fof(f3101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3437,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f3181,f3280])).

fof(f3280,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f3102])).

fof(f3102,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f3063,f3101,f3100])).

fof(f3063,plain,(
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
    inference(flattening,[],[f3062])).

fof(f3062,plain,(
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
    inference(ennf_transformation,[],[f3018])).

fof(f3018,plain,(
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
    inference(rectify,[],[f2973])).

fof(f2973,axiom,(
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

fof(f4151,plain,
    ( ~ spl34_1
    | spl34_3
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(avatar_contradiction_clause,[],[f4150])).

fof(f4150,plain,
    ( $false
    | ~ spl34_1
    | spl34_3
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f4149,f3899])).

fof(f3899,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | spl34_3
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3898,f3356])).

fof(f3356,plain,
    ( sK3 != k2_yellow_0(sK2,sK4)
    | spl34_3 ),
    inference(avatar_component_clause,[],[f3354])).

fof(f3354,plain,
    ( spl34_3
  <=> sK3 = k2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_3])])).

fof(f3898,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3897,f3182])).

fof(f3897,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3872,f3443])).

fof(f3443,plain,(
    ! [X76] : m1_subset_1(k2_yellow_0(sK2,X76),u1_struct_0(sK2)) ),
    inference(resolution,[],[f3181,f3314])).

fof(f3314,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3083])).

fof(f3083,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2977])).

fof(f2977,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f3872,plain,
    ( ~ r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(resolution,[],[f3395,f3673])).

fof(f3673,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),sK3)
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3667,f3443])).

fof(f3667,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,k2_yellow_0(sK2,sK4),sK3)
    | ~ spl34_4
    | ~ spl34_7 ),
    inference(resolution,[],[f3638,f3374])).

fof(f3638,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
    | ~ spl34_4 ),
    inference(resolution,[],[f3559,f3359])).

fof(f3359,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl34_4 ),
    inference(avatar_component_clause,[],[f3358])).

fof(f3559,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f3556,f3181])).

fof(f3556,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3443,f3338])).

fof(f3338,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3253])).

fof(f3253,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3142])).

fof(f3142,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK18(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK18(X0,X1,X2))
                & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f3140,f3141])).

fof(f3141,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK18(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK18(X0,X1,X2))
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3140,plain,(
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
    inference(rectify,[],[f3139])).

fof(f3139,plain,(
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
    inference(flattening,[],[f3138])).

fof(f3138,plain,(
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
    inference(nnf_transformation,[],[f3060])).

fof(f3060,plain,(
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
    inference(flattening,[],[f3059])).

fof(f3059,plain,(
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
    inference(ennf_transformation,[],[f2968])).

fof(f2968,axiom,(
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

fof(f4149,plain,
    ( r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ spl34_1
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f4146,f3182])).

fof(f4146,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ spl34_1
    | ~ spl34_4 ),
    inference(resolution,[],[f4087,f3347])).

fof(f4087,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,k2_yellow_0(sK2,sK4)) )
    | ~ spl34_4 ),
    inference(resolution,[],[f3560,f3359])).

fof(f3560,plain,(
    ! [X2,X1] :
      ( ~ r2_yellow_0(sK2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X1,X2)
      | r1_orders_2(sK2,X2,k2_yellow_0(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f3557,f3181])).

fof(f3557,plain,(
    ! [X2,X1] :
      ( ~ r1_lattice3(sK2,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X1)
      | r1_orders_2(sK2,X2,k2_yellow_0(sK2,X1))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f3443,f3337])).

fof(f3337,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3254])).

fof(f3254,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3142])).

fof(f3647,plain,
    ( spl34_2
    | ~ spl34_5
    | ~ spl34_6
    | ~ spl34_7 ),
    inference(avatar_contradiction_clause,[],[f3646])).

fof(f3646,plain,
    ( $false
    | spl34_2
    | ~ spl34_5
    | ~ spl34_6
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3645,f3352])).

fof(f3352,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | spl34_2 ),
    inference(avatar_component_clause,[],[f3350])).

fof(f3350,plain,
    ( spl34_2
  <=> r1_orders_2(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_2])])).

fof(f3645,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl34_5
    | ~ spl34_6
    | ~ spl34_7 ),
    inference(subsumption_resolution,[],[f3641,f3370])).

fof(f3370,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl34_6 ),
    inference(avatar_component_clause,[],[f3368])).

fof(f3368,plain,
    ( spl34_6
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_6])])).

fof(f3641,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK3)
    | ~ spl34_5
    | ~ spl34_7 ),
    inference(resolution,[],[f3374,f3365])).

fof(f3365,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ spl34_5 ),
    inference(avatar_component_clause,[],[f3363])).

fof(f3363,plain,
    ( spl34_5
  <=> r1_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_5])])).

fof(f3637,plain,
    ( spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_6 ),
    inference(avatar_contradiction_clause,[],[f3636])).

fof(f3636,plain,
    ( $false
    | spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_6 ),
    inference(subsumption_resolution,[],[f3635,f3352])).

fof(f3635,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_6 ),
    inference(subsumption_resolution,[],[f3631,f3370])).

fof(f3631,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK3)
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5 ),
    inference(resolution,[],[f3507,f3365])).

fof(f3507,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3) )
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f3506,f3181])).

fof(f3506,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f3505,f3359])).

fof(f3505,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl34_3 ),
    inference(subsumption_resolution,[],[f3499,f3182])).

fof(f3499,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,sK4)
        | r1_orders_2(sK2,X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl34_3 ),
    inference(superposition,[],[f3337,f3355])).

fof(f3355,plain,
    ( sK3 = k2_yellow_0(sK2,sK4)
    | ~ spl34_3 ),
    inference(avatar_component_clause,[],[f3354])).

fof(f3546,plain,
    ( spl34_16
    | spl34_17
    | spl34_21
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f3545,f3346,f3542,f3520,f3516])).

fof(f3545,plain,
    ( ! [X1] :
        ( r1_orders_2(sK2,X1,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
        | sP0(sK2,sK4) )
    | ~ spl34_1 ),
    inference(subsumption_resolution,[],[f3513,f3182])).

fof(f3513,plain,
    ( ! [X1] :
        ( r1_orders_2(sK2,X1,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
        | sP0(sK2,sK4)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2)) )
    | ~ spl34_1 ),
    inference(resolution,[],[f3347,f3275])).

fof(f3275,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_orders_2(X0,X4,sK19(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK20(X0,X1,X2))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3544,plain,
    ( spl34_16
    | spl34_19
    | spl34_21
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f3540,f3346,f3542,f3530,f3516])).

fof(f3540,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
        | sP0(sK2,sK4) )
    | ~ spl34_1 ),
    inference(subsumption_resolution,[],[f3512,f3182])).

fof(f3512,plain,
    ( ! [X0] :
        ( r1_orders_2(sK2,X0,sK19(sK2,sK4,sK3))
        | ~ r1_lattice3(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
        | sP0(sK2,sK4)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2)) )
    | ~ spl34_1 ),
    inference(resolution,[],[f3347,f3274])).

fof(f3274,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_orders_2(X0,X4,sK19(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3539,plain,
    ( spl34_16
    | spl34_17
    | spl34_20
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f3538,f3346,f3534,f3520,f3516])).

fof(f3538,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | sP0(sK2,sK4)
    | ~ spl34_1 ),
    inference(subsumption_resolution,[],[f3511,f3182])).

fof(f3511,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1 ),
    inference(resolution,[],[f3347,f3272])).

fof(f3272,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK19(X0,X1,X2))
      | r1_lattice3(X0,X1,sK20(X0,X1,X2))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3537,plain,
    ( spl34_16
    | spl34_19
    | spl34_20
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f3528,f3346,f3534,f3530,f3516])).

fof(f3528,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ spl34_1 ),
    inference(subsumption_resolution,[],[f3510,f3182])).

fof(f3510,plain,
    ( r1_lattice3(sK2,sK4,sK19(sK2,sK4,sK3))
    | m1_subset_1(sK20(sK2,sK4,sK3),u1_struct_0(sK2))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1 ),
    inference(resolution,[],[f3347,f3271])).

fof(f3271,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK19(X0,X1,X2))
      | m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3527,plain,
    ( spl34_16
    | spl34_17
    | spl34_18
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f3514,f3346,f3524,f3520,f3516])).

fof(f3514,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | sP0(sK2,sK4)
    | ~ spl34_1 ),
    inference(subsumption_resolution,[],[f3509,f3182])).

fof(f3509,plain,
    ( m1_subset_1(sK19(sK2,sK4,sK3),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK4,sK20(sK2,sK4,sK3))
    | sP0(sK2,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl34_1 ),
    inference(resolution,[],[f3347,f3269])).

fof(f3269,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK20(X0,X1,X2))
      | sP0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3150])).

fof(f3504,plain,
    ( spl34_1
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(avatar_contradiction_clause,[],[f3503])).

fof(f3503,plain,
    ( $false
    | spl34_1
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f3502,f3181])).

fof(f3502,plain,
    ( ~ l1_orders_2(sK2)
    | spl34_1
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f3501,f3348])).

fof(f3348,plain,
    ( ~ r1_lattice3(sK2,sK4,sK3)
    | spl34_1 ),
    inference(avatar_component_clause,[],[f3346])).

fof(f3501,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(subsumption_resolution,[],[f3500,f3359])).

fof(f3500,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl34_3 ),
    inference(subsumption_resolution,[],[f3498,f3182])).

fof(f3498,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl34_3 ),
    inference(superposition,[],[f3338,f3355])).

fof(f3381,plain,
    ( spl34_3
    | spl34_1 ),
    inference(avatar_split_clause,[],[f3183,f3346,f3354])).

fof(f3183,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | sK3 = k2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3380,plain,
    ( spl34_4
    | spl34_1 ),
    inference(avatar_split_clause,[],[f3184,f3346,f3358])).

fof(f3184,plain,
    ( r1_lattice3(sK2,sK4,sK3)
    | r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3379,plain,
    ( spl34_3
    | spl34_7 ),
    inference(avatar_split_clause,[],[f3188,f3373,f3354])).

fof(f3188,plain,(
    ! [X3] :
      ( r1_orders_2(sK2,X3,sK3)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | sK3 = k2_yellow_0(sK2,sK4) ) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3378,plain,
    ( spl34_4
    | spl34_7 ),
    inference(avatar_split_clause,[],[f3189,f3373,f3358])).

fof(f3189,plain,(
    ! [X3] :
      ( r1_orders_2(sK2,X3,sK3)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | r2_yellow_0(sK2,sK4) ) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3377,plain,
    ( ~ spl34_1
    | spl34_6
    | spl34_7 ),
    inference(avatar_split_clause,[],[f3190,f3373,f3368,f3346])).

fof(f3190,plain,(
    ! [X3] :
      ( r1_orders_2(sK2,X3,sK3)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK4,sK3) ) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3376,plain,
    ( ~ spl34_1
    | spl34_5
    | spl34_7 ),
    inference(avatar_split_clause,[],[f3191,f3373,f3363,f3346])).

fof(f3191,plain,(
    ! [X3] :
      ( r1_orders_2(sK2,X3,sK3)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | r1_lattice3(sK2,sK4,sK5)
      | ~ r1_lattice3(sK2,sK4,sK3) ) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3375,plain,
    ( ~ spl34_1
    | ~ spl34_2
    | spl34_7 ),
    inference(avatar_split_clause,[],[f3192,f3373,f3350,f3346])).

fof(f3192,plain,(
    ! [X3] :
      ( r1_orders_2(sK2,X3,sK3)
      | ~ r1_lattice3(sK2,sK4,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK5,sK3)
      | ~ r1_lattice3(sK2,sK4,sK3) ) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3371,plain,
    ( ~ spl34_1
    | spl34_6
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(avatar_split_clause,[],[f3195,f3358,f3354,f3368,f3346])).

fof(f3195,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | sK3 != k2_yellow_0(sK2,sK4)
    | m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3366,plain,
    ( ~ spl34_1
    | spl34_5
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(avatar_split_clause,[],[f3196,f3358,f3354,f3363,f3346])).

fof(f3196,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | sK3 != k2_yellow_0(sK2,sK4)
    | r1_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f3107])).

fof(f3361,plain,
    ( ~ spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4 ),
    inference(avatar_split_clause,[],[f3197,f3358,f3354,f3350,f3346])).

fof(f3197,plain,
    ( ~ r2_yellow_0(sK2,sK4)
    | sK3 != k2_yellow_0(sK2,sK4)
    | ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_lattice3(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f3107])).
%------------------------------------------------------------------------------
