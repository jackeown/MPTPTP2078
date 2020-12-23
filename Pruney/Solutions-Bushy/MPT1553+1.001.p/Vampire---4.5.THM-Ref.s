%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1553+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 574 expanded)
%              Number of leaves         :   21 ( 217 expanded)
%              Depth                    :   25
%              Number of atoms          :  942 (5863 expanded)
%              Number of equality atoms :   46 ( 686 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f116,f138,f220,f249,f256,f264,f273,f283,f427,f463,f487,f505])).

fof(f505,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f503,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( ( ~ r2_yellow_0(sK0,sK2)
          | sK1 != k2_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,X3,sK1)
            | ~ r1_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_lattice3(sK0,sK2,sK1) )
      | ( ( ( ~ r1_orders_2(sK0,sK3,sK1)
            & r1_lattice3(sK0,sK2,sK3)
            & m1_subset_1(sK3,u1_struct_0(sK0)) )
          | ~ r1_lattice3(sK0,sK2,sK1) )
        & r2_yellow_0(sK0,sK2)
        & sK1 = k2_yellow_0(sK0,sK2) ) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
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
              ( ( ( ~ r2_yellow_0(sK0,X2)
                  | k2_yellow_0(sK0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(sK0,X3,X1)
                    | ~ r1_lattice3(sK0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
                & r1_lattice3(sK0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(sK0,X4,X1)
                      & r1_lattice3(sK0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  | ~ r1_lattice3(sK0,X2,X1) )
                & r2_yellow_0(sK0,X2)
                & k2_yellow_0(sK0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r2_yellow_0(sK0,X2)
                | k2_yellow_0(sK0,X2) != X1 )
              & ! [X3] :
                  ( r1_orders_2(sK0,X3,X1)
                  | ~ r1_lattice3(sK0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & r1_lattice3(sK0,X2,X1) )
            | ( ( ? [X4] :
                    ( ~ r1_orders_2(sK0,X4,X1)
                    & r1_lattice3(sK0,X2,X4)
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                | ~ r1_lattice3(sK0,X2,X1) )
              & r2_yellow_0(sK0,X2)
              & k2_yellow_0(sK0,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r2_yellow_0(sK0,X2)
              | k2_yellow_0(sK0,X2) != sK1 )
            & ! [X3] :
                ( r1_orders_2(sK0,X3,sK1)
                | ~ r1_lattice3(sK0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & r1_lattice3(sK0,X2,sK1) )
          | ( ( ? [X4] :
                  ( ~ r1_orders_2(sK0,X4,sK1)
                  & r1_lattice3(sK0,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r1_lattice3(sK0,X2,sK1) )
            & r2_yellow_0(sK0,X2)
            & k2_yellow_0(sK0,X2) = sK1 ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ( ~ r2_yellow_0(sK0,X2)
            | k2_yellow_0(sK0,X2) != sK1 )
          & ! [X3] :
              ( r1_orders_2(sK0,X3,sK1)
              | ~ r1_lattice3(sK0,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & r1_lattice3(sK0,X2,sK1) )
        | ( ( ? [X4] :
                ( ~ r1_orders_2(sK0,X4,sK1)
                & r1_lattice3(sK0,X2,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r1_lattice3(sK0,X2,sK1) )
          & r2_yellow_0(sK0,X2)
          & k2_yellow_0(sK0,X2) = sK1 ) )
   => ( ( ( ~ r2_yellow_0(sK0,sK2)
          | sK1 != k2_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,X3,sK1)
            | ~ r1_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_lattice3(sK0,sK2,sK1) )
      | ( ( ? [X4] :
              ( ~ r1_orders_2(sK0,X4,sK1)
              & r1_lattice3(sK0,sK2,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r1_lattice3(sK0,sK2,sK1) )
        & r2_yellow_0(sK0,sK2)
        & sK1 = k2_yellow_0(sK0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X4] :
        ( ~ r1_orders_2(sK0,X4,sK1)
        & r1_lattice3(sK0,sK2,X4)
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK3,sK1)
      & r1_lattice3(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f503,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f502,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f502,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f501,f86])).

fof(f86,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_1
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f501,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_2
    | spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f500,f90])).

fof(f90,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_2
  <=> r1_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f500,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f497,f466])).

fof(f466,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | spl8_4 ),
    inference(resolution,[],[f137,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(X1,X0)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f137,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_4
  <=> sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f497,plain,
    ( sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_11 ),
    inference(resolution,[],[f238,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f47,f58])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f238,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl8_11
  <=> m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f487,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f485,f29])).

fof(f485,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f484,f466])).

fof(f484,plain,
    ( sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f483,f90])).

fof(f483,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_4
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f482,f237])).

fof(f237,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f482,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_4
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f478,f233])).

fof(f233,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl8_10
  <=> r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f478,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK1))
    | ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f472,f199])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK2,X0),X0)
        | ~ r1_lattice3(sK0,sK2,X0)
        | sQ7_eqProxy(k2_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f198,f28])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK2,X0),X0)
        | ~ r1_lattice3(sK0,sK2,X0)
        | sQ7_eqProxy(k2_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f66,f86])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f49,f58])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f472,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,X3,sK1)
        | ~ r1_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl8_4 ),
    inference(subsumption_resolution,[],[f64,f137])).

fof(f64,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,X3,sK1)
      | ~ r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2)) ) ),
    inference(equality_proxy_replacement,[],[f35,f58])).

fof(f35,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,X3,sK1)
      | ~ r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK1 = k2_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f463,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f461,f28])).

fof(f461,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f460,f215])).

fof(f215,plain,
    ( m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl8_8
  <=> m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f460,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f457,f86])).

fof(f457,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f446,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f446,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f439,f136])).

fof(f136,plain,
    ( sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f439,plain,
    ( ! [X2] :
        ( ~ sQ7_eqProxy(sK1,X2)
        | ~ r1_lattice3(sK0,sK2,X2) )
    | spl8_2 ),
    inference(resolution,[],[f431,f81])).

fof(f431,plain,
    ( ! [X0] :
        ( ~ sQ7_eqProxy(X0,sK1)
        | ~ r1_lattice3(sK0,sK2,X0) )
    | spl8_2 ),
    inference(resolution,[],[f428,f80])).

fof(f80,plain,(
    ! [X0] : sQ7_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( ~ sQ7_eqProxy(X1,sK2)
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ sQ7_eqProxy(X0,sK1) )
    | spl8_2 ),
    inference(resolution,[],[f421,f80])).

fof(f421,plain,
    ( ! [X2,X0,X1] :
        ( ~ sQ7_eqProxy(X2,sK0)
        | ~ sQ7_eqProxy(X1,sK1)
        | ~ r1_lattice3(X2,X0,X1)
        | ~ sQ7_eqProxy(X0,sK2) )
    | spl8_2 ),
    inference(resolution,[],[f89,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_lattice3(X1,X3,X5)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X4,X5)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f89,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f427,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f424,f136])).

fof(f424,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | ~ spl8_3
    | spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(resolution,[],[f409,f81])).

fof(f409,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ spl8_3
    | spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f408,f133])).

fof(f133,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f408,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl8_5
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f400,f180])).

fof(f180,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl8_7
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f400,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl8_5
    | ~ spl8_9 ),
    inference(resolution,[],[f392,f219])).

fof(f219,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3,X0)
        | ~ sQ7_eqProxy(X0,sK1) )
    | spl8_5 ),
    inference(resolution,[],[f389,f80])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ sQ7_eqProxy(X1,sK3)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ sQ7_eqProxy(X0,sK1) )
    | spl8_5 ),
    inference(resolution,[],[f285,f80])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ sQ7_eqProxy(X2,sK0)
        | ~ sQ7_eqProxy(X1,sK1)
        | ~ r1_orders_2(X2,X0,X1)
        | ~ sQ7_eqProxy(X0,sK3) )
    | spl8_5 ),
    inference(resolution,[],[f168,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X3,X5)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ sQ7_eqProxy(X4,X5)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f168,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_5
  <=> r1_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f283,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f281,f167])).

fof(f167,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f281,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f280,f90])).

fof(f280,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f279,f136])).

fof(f279,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f59,f86])).

fof(f59,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(equality_proxy_replacement,[],[f44,f58])).

fof(f44,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | sK1 != k2_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f273,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f271,f90])).

fof(f271,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_1
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f259,f136])).

fof(f259,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f258,f179])).

fof(f179,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f258,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f60,f86])).

fof(f60,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(equality_proxy_replacement,[],[f43,f58])).

fof(f43,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | sK1 != k2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f264,plain,
    ( ~ spl8_4
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl8_4
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f29,f80,f216,f136,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X1,X3)
      | ~ sQ7_eqProxy(X2,X3)
      | ~ m1_subset_1(X0,X2)
      | ~ sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f58])).

fof(f216,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f256,plain,
    ( spl8_2
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl8_2
    | spl8_4 ),
    inference(subsumption_resolution,[],[f253,f89])).

fof(f253,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f65,f137])).

fof(f65,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f30,f58])).

fof(f30,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f249,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f247,f28])).

fof(f247,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f246,f29])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f245,f86])).

fof(f245,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_2
    | spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f244,f90])).

fof(f244,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f241,f141])).

fof(f141,plain,
    ( ~ sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | spl8_4 ),
    inference(resolution,[],[f137,f81])).

fof(f241,plain,
    ( sQ7_eqProxy(k2_yellow_0(sK0,sK2),sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_10 ),
    inference(resolution,[],[f234,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | sQ7_eqProxy(k2_yellow_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_proxy_replacement,[],[f48,f58])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X1) = X2
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f234,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f220,plain,
    ( ~ spl8_8
    | spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f126,f84,f218,f214])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f138,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f129,f88,f84,f135,f131])).

fof(f129,plain,
    ( ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f120,f86])).

fof(f120,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f61,f90])).

fof(f61,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ sQ7_eqProxy(sK1,k2_yellow_0(sK0,sK2))
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(equality_proxy_replacement,[],[f42,f58])).

fof(f42,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | sK1 != k2_yellow_0(sK0,sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,
    ( ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f113,f28])).

fof(f113,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f112,f29])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f111,f90])).

fof(f111,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f108,f85])).

fof(f85,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f108,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK6(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK6(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f106,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f105,f27])).

fof(f105,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f103,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f102,f90])).

fof(f102,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f101,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_1 ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,sK5(sK0,X0,sK1))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,sK2,sK5(sK0,X0,sK1))
        | ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0)) )
    | spl8_1 ),
    inference(resolution,[],[f95,f92])).

fof(f92,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,X3,sK1)
        | ~ r1_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl8_1 ),
    inference(subsumption_resolution,[],[f36,f85])).

fof(f36,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,X3,sK1)
      | ~ r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X1)
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_yellow_0(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X1)
      | ~ r1_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r2_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f55,f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f31,f88,f84])).

fof(f31,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
