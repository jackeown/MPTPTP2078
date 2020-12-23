%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1480+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 5.84s
% Output     : Refutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 780 expanded)
%              Number of leaves         :   19 ( 298 expanded)
%              Depth                    :   36
%              Number of atoms          : 1009 (6166 expanded)
%              Number of equality atoms :   79 ( 717 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9959,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3059,f3065,f3071,f3410,f3412,f5301,f9958])).

fof(f9958,plain,
    ( ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11
    | ~ spl20_62 ),
    inference(avatar_contradiction_clause,[],[f9957])).

fof(f9957,plain,
    ( $false
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11
    | ~ spl20_62 ),
    inference(subsumption_resolution,[],[f9956,f2955])).

fof(f2955,plain,(
    k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f2901])).

fof(f2901,plain,
    ( k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f2860,f2900,f2899,f2898])).

fof(f2898,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(sK1,X1,X2) != k10_lattice3(sK1,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2899,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k10_lattice3(sK1,X1,X2) != k10_lattice3(sK1,X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( k10_lattice3(sK1,sK2,X2) != k10_lattice3(sK1,X2,sK2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2900,plain,
    ( ? [X2] :
        ( k10_lattice3(sK1,sK2,X2) != k10_lattice3(sK1,X2,sK2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( k10_lattice3(sK1,sK2,sK3) != k10_lattice3(sK1,sK3,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2860,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f2859])).

fof(f2859,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2842])).

fof(f2842,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f2841])).

fof(f2841,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

fof(f9956,plain,
    ( k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11
    | ~ spl20_62 ),
    inference(subsumption_resolution,[],[f9955,f2954])).

fof(f2954,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2901])).

fof(f9955,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11
    | ~ spl20_62 ),
    inference(subsumption_resolution,[],[f9954,f2953])).

fof(f2953,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2901])).

fof(f9954,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11
    | ~ spl20_62 ),
    inference(subsumption_resolution,[],[f9938,f5252])).

fof(f5252,plain,
    ( m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ spl20_62 ),
    inference(avatar_component_clause,[],[f5251])).

fof(f5251,plain,
    ( spl20_62
  <=> m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_62])])).

fof(f9938,plain,
    ( ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = k10_lattice3(sK1,sK3,sK2)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11 ),
    inference(superposition,[],[f5937,f9691])).

fof(f9691,plain,
    ( k10_lattice3(sK1,sK3,sK2) = sK19(sK1,sK2,sK3)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11 ),
    inference(subsumption_resolution,[],[f9690,f2953])).

fof(f9690,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK3,sK2) = sK19(sK1,sK2,sK3)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11 ),
    inference(subsumption_resolution,[],[f9678,f2954])).

fof(f9678,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK3,sK2) = sK19(sK1,sK2,sK3)
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4
    | ~ spl20_11 ),
    inference(resolution,[],[f5884,f3360])).

fof(f3360,plain,
    ( m1_subset_1(sK19(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl20_11 ),
    inference(avatar_component_clause,[],[f3359])).

fof(f3359,plain,
    ( spl20_11
  <=> m1_subset_1(sK19(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_11])])).

fof(f5884,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k10_lattice3(sK1,X3,X2) = sK19(sK1,X2,X3) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f5883,f3073])).

fof(f3073,plain,(
    ! [X12,X11] :
      ( r1_orders_2(sK1,X11,sK19(sK1,X12,X11))
      | ~ m1_subset_1(X12,u1_struct_0(sK1))
      | ~ m1_subset_1(X11,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f2952,f3043])).

fof(f3043,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK1))
      | ~ m1_subset_1(X12,u1_struct_0(sK1))
      | r1_orders_2(sK1,X11,sK19(sK1,X12,X11))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f2951,f3012])).

fof(f3012,plain,(
    ! [X6,X0,X5] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X6,sK19(X0,X5,X6))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2948])).

fof(f2948,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,X3,sK18(X0,X3))
                  & r1_orders_2(X0,sK17(X0),sK18(X0,X3))
                  & r1_orders_2(X0,sK16(X0),sK18(X0,X3))
                  & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,sK17(X0),X3)
                | ~ r1_orders_2(X0,sK16(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK17(X0),u1_struct_0(X0))
            & m1_subset_1(sK16(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,sK19(X0,X5,X6),X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,sK19(X0,X5,X6))
                    & r1_orders_2(X0,X5,sK19(X0,X5,X6))
                    & m1_subset_1(sK19(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19])],[f2943,f2947,f2946,f2945,f2944])).

fof(f2944,plain,(
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
                    & r1_orders_2(X0,sK16(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK16(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK16(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2945,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,sK16(X0),X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,sK16(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK17(X0),X4)
                & r1_orders_2(X0,sK16(X0),X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK17(X0),X3)
            | ~ r1_orders_2(X0,sK16(X0),X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK17(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2946,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,sK17(X0),X4)
          & r1_orders_2(X0,sK16(X0),X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK18(X0,X3))
        & r1_orders_2(X0,sK17(X0),sK18(X0,X3))
        & r1_orders_2(X0,sK16(X0),sK18(X0,X3))
        & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2947,plain,(
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
            ( r1_orders_2(X0,sK19(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK19(X0,X5,X6))
        & r1_orders_2(X0,X5,sK19(X0,X5,X6))
        & m1_subset_1(sK19(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2943,plain,(
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
    inference(rectify,[],[f2942])).

fof(f2942,plain,(
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
    inference(nnf_transformation,[],[f2892])).

fof(f2892,plain,(
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
    inference(flattening,[],[f2891])).

fof(f2891,plain,(
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
    inference(ennf_transformation,[],[f2808])).

fof(f2808,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_lattice3)).

fof(f2951,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f2901])).

fof(f2952,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f2901])).

fof(f5883,plain,
    ( ! [X2,X3] :
        ( k10_lattice3(sK1,X3,X2) = sK19(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X2,X3)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f5880,f3072])).

fof(f3072,plain,(
    ! [X10,X9] :
      ( r1_orders_2(sK1,X10,sK19(sK1,X10,X9))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | ~ m1_subset_1(X9,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f2952,f3042])).

fof(f3042,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK1))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | r1_orders_2(sK1,X10,sK19(sK1,X10,X9))
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f2951,f3011])).

fof(f3011,plain,(
    ! [X6,X0,X5] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,sK19(X0,X5,X6))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2948])).

fof(f5880,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK1,X2,sK19(sK1,X2,X3))
        | k10_lattice3(sK1,X3,X2) = sK19(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X2,X3)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f5877])).

fof(f5877,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK1,X2,sK19(sK1,X2,X3))
        | k10_lattice3(sK1,X3,X2) = sK19(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | k10_lattice3(sK1,X3,X2) = sK19(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK19(sK1,X2,X3)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(resolution,[],[f4539,f3064])).

fof(f3064,plain,
    ( ! [X4,X5,X3] :
        ( r1_orders_2(sK1,X3,sK9(sK1,X4,X3,X5))
        | k10_lattice3(sK1,X4,X3) = X5
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X4,X5)
        | ~ r1_orders_2(sK1,X3,X5) )
    | ~ spl20_3 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f3063,plain,
    ( spl20_3
  <=> ! [X3,X5,X4] :
        ( r1_orders_2(sK1,X3,sK9(sK1,X4,X3,X5))
        | k10_lattice3(sK1,X4,X3) = X5
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X4,X5)
        | ~ r1_orders_2(sK1,X3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f4539,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X0)))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X0))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X0),u1_struct_0(sK1)) )
    | ~ spl20_2
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f4538,f3073])).

fof(f4538,plain,
    ( ! [X2,X0,X1] :
        ( k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X0)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X0))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X0))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X0),u1_struct_0(sK1)) )
    | ~ spl20_2
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f4533])).

fof(f4533,plain,
    ( ! [X2,X0,X1] :
        ( k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X0)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X0))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X0))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X0),u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X0),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X0))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X0)) )
    | ~ spl20_2
    | ~ spl20_4 ),
    inference(resolution,[],[f3865,f3058])).

fof(f3058,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK1,X0,sK9(sK1,X0,X1,X2))
        | k10_lattice3(sK1,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X2)
        | ~ r1_orders_2(sK1,X1,X2) )
    | ~ spl20_2 ),
    inference(avatar_component_clause,[],[f3057])).

fof(f3057,plain,
    ( spl20_2
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK1,X0,sK9(sK1,X0,X1,X2))
        | k10_lattice3(sK1,X0,X1) = X2
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,X2)
        | ~ r1_orders_2(sK1,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_2])])).

fof(f3865,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1)) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3864,f3076])).

fof(f3076,plain,(
    ~ v2_struct_0(sK1) ),
    inference(global_subsumption,[],[f2952,f3046])).

fof(f3046,plain,
    ( ~ v2_struct_0(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f2951,f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2895])).

fof(f2895,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2894])).

fof(f2894,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2806])).

fof(f2806,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f3864,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3863,f2950])).

fof(f2950,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f2901])).

fof(f3863,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ v5_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3862,f2951])).

fof(f3862,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3861,f2952])).

fof(f3861,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f3860])).

fof(f3860,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X1,X0,sK19(sK1,X2,X3)))
        | k10_lattice3(sK1,X1,X0) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ m1_subset_1(sK19(sK1,X2,X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl20_4 ),
    inference(resolution,[],[f3232,f2978])).

fof(f2978,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2925])).

fof(f2925,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK9(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK9(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK9(X0,X1,X2,X3))
                        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f2923,f2924])).

fof(f2924,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK9(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK9(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK9(X0,X1,X2,X3))
        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2923,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
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
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2922])).

fof(f2922,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2921])).

fof(f2921,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2872])).

fof(f2872,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2871])).

fof(f2871,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2835])).

fof(f2835,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(f3232,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK9(sK1,X0,X1,sK19(sK1,X2,X3)),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X0,X1,sK19(sK1,X2,X3))) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3231,f2952])).

fof(f3231,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK9(sK1,X0,X1,sK19(sK1,X2,X3)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ l1_orders_2(sK1) )
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f3230,f2951])).

fof(f3230,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK9(sK1,X0,X1,sK19(sK1,X2,X3)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ v1_lattice3(sK1)
        | ~ l1_orders_2(sK1) )
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f3229])).

fof(f3229,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X2,X3)
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X2,X3))
        | ~ r1_orders_2(sK1,X2,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(sK9(sK1,X0,X1,sK19(sK1,X2,X3)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK9(sK1,X0,X1,sK19(sK1,X2,X3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ v1_lattice3(sK1)
        | ~ l1_orders_2(sK1) )
    | ~ spl20_4 ),
    inference(resolution,[],[f3132,f3010])).

fof(f3010,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK19(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2948])).

fof(f3132,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK19(sK1,X6,X7),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k10_lattice3(sK1,X4,X5) = sK19(sK1,X6,X7)
        | ~ r1_orders_2(sK1,X4,sK19(sK1,X6,X7))
        | ~ r1_orders_2(sK1,X5,sK19(sK1,X6,X7))
        | ~ r1_orders_2(sK1,X6,sK9(sK1,X4,X5,sK19(sK1,X6,X7)))
        | ~ m1_subset_1(sK9(sK1,X4,X5,sK19(sK1,X6,X7)),u1_struct_0(sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X7,sK9(sK1,X4,X5,sK19(sK1,X6,X7))) )
    | ~ spl20_4 ),
    inference(resolution,[],[f3070,f3074])).

fof(f3074,plain,(
    ! [X14,X15,X13] :
      ( r1_orders_2(sK1,sK19(sK1,X15,X13),X14)
      | ~ r1_orders_2(sK1,X15,X14)
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | ~ m1_subset_1(X15,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X13,X14) ) ),
    inference(global_subsumption,[],[f2952,f3044])).

fof(f3044,plain,(
    ! [X14,X15,X13] :
      ( ~ r1_orders_2(sK1,X13,X14)
      | ~ r1_orders_2(sK1,X15,X14)
      | ~ m1_subset_1(X14,u1_struct_0(sK1))
      | ~ m1_subset_1(X13,u1_struct_0(sK1))
      | ~ m1_subset_1(X15,u1_struct_0(sK1))
      | r1_orders_2(sK1,sK19(sK1,X15,X13),X14)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f2951,f3013])).

fof(f3013,plain,(
    ! [X6,X0,X8,X5] :
      ( ~ v1_lattice3(X0)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,sK19(X0,X5,X6),X8)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2948])).

fof(f3070,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK1,X6,sK9(sK1,X7,X8,X6))
        | k10_lattice3(sK1,X7,X8) = X6
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X7,X6)
        | ~ r1_orders_2(sK1,X8,X6) )
    | ~ spl20_4 ),
    inference(avatar_component_clause,[],[f3069])).

fof(f3069,plain,
    ( spl20_4
  <=> ! [X7,X8,X6] :
        ( ~ r1_orders_2(sK1,X6,sK9(sK1,X7,X8,X6))
        | k10_lattice3(sK1,X7,X8) = X6
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X7,X6)
        | ~ r1_orders_2(sK1,X8,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f5937,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK19(sK1,X0,X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X0,X1) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f5936,f3073])).

fof(f5936,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK1,X0,X1) = sK19(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X0,X1),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X0,X1)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f5935,f3072])).

fof(f5935,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,sK19(sK1,X0,X1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X0,X1),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X0,X1)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f5930])).

fof(f5930,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,sK19(sK1,X0,X1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X0,X1),u1_struct_0(sK1))
        | k10_lattice3(sK1,X0,X1) = sK19(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X0,X1),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X0,sK19(sK1,X0,X1))
        | ~ r1_orders_2(sK1,X1,sK19(sK1,X0,X1)) )
    | ~ spl20_2
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(resolution,[],[f4540,f3058])).

fof(f4540,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK1,X5,sK9(sK1,X3,X4,sK19(sK1,X5,X4)))
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X5,X4))
        | k10_lattice3(sK1,X3,X4) = sK19(sK1,X5,X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X5,X4),u1_struct_0(sK1)) )
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(subsumption_resolution,[],[f4537,f3073])).

fof(f4537,plain,
    ( ! [X4,X5,X3] :
        ( k10_lattice3(sK1,X3,X4) = sK19(sK1,X5,X4)
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X5,X4))
        | ~ r1_orders_2(sK1,X4,sK19(sK1,X5,X4))
        | ~ r1_orders_2(sK1,X5,sK9(sK1,X3,X4,sK19(sK1,X5,X4)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X5,X4),u1_struct_0(sK1)) )
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(duplicate_literal_removal,[],[f4534])).

fof(f4534,plain,
    ( ! [X4,X5,X3] :
        ( k10_lattice3(sK1,X3,X4) = sK19(sK1,X5,X4)
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X5,X4))
        | ~ r1_orders_2(sK1,X4,sK19(sK1,X5,X4))
        | ~ r1_orders_2(sK1,X5,sK9(sK1,X3,X4,sK19(sK1,X5,X4)))
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X5,X4),u1_struct_0(sK1))
        | k10_lattice3(sK1,X3,X4) = sK19(sK1,X5,X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK19(sK1,X5,X4),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,X3,sK19(sK1,X5,X4))
        | ~ r1_orders_2(sK1,X4,sK19(sK1,X5,X4)) )
    | ~ spl20_3
    | ~ spl20_4 ),
    inference(resolution,[],[f3865,f3064])).

fof(f5301,plain,(
    spl20_62 ),
    inference(avatar_contradiction_clause,[],[f5300])).

fof(f5300,plain,
    ( $false
    | spl20_62 ),
    inference(subsumption_resolution,[],[f5299,f2952])).

fof(f5299,plain,
    ( ~ l1_orders_2(sK1)
    | spl20_62 ),
    inference(subsumption_resolution,[],[f5298,f2954])).

fof(f5298,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl20_62 ),
    inference(subsumption_resolution,[],[f5297,f2953])).

fof(f5297,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl20_62 ),
    inference(resolution,[],[f5253,f2974])).

fof(f2974,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2870])).

fof(f2870,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2869])).

fof(f2869,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2820])).

fof(f2820,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f5253,plain,
    ( ~ m1_subset_1(k10_lattice3(sK1,sK3,sK2),u1_struct_0(sK1))
    | spl20_62 ),
    inference(avatar_component_clause,[],[f5251])).

fof(f3412,plain,(
    ~ spl20_1 ),
    inference(avatar_contradiction_clause,[],[f3411])).

fof(f3411,plain,
    ( $false
    | ~ spl20_1 ),
    inference(subsumption_resolution,[],[f3055,f3076])).

fof(f3055,plain,
    ( v2_struct_0(sK1)
    | ~ spl20_1 ),
    inference(avatar_component_clause,[],[f3053])).

fof(f3053,plain,
    ( spl20_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f3410,plain,(
    spl20_11 ),
    inference(avatar_contradiction_clause,[],[f3409])).

fof(f3409,plain,
    ( $false
    | spl20_11 ),
    inference(subsumption_resolution,[],[f3408,f2952])).

fof(f3408,plain,
    ( ~ l1_orders_2(sK1)
    | spl20_11 ),
    inference(subsumption_resolution,[],[f3407,f2951])).

fof(f3407,plain,
    ( ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | spl20_11 ),
    inference(subsumption_resolution,[],[f3406,f2953])).

fof(f3406,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | spl20_11 ),
    inference(subsumption_resolution,[],[f3405,f2954])).

fof(f3405,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | spl20_11 ),
    inference(resolution,[],[f3361,f3010])).

fof(f3361,plain,
    ( ~ m1_subset_1(sK19(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl20_11 ),
    inference(avatar_component_clause,[],[f3359])).

fof(f3071,plain,
    ( spl20_1
    | spl20_4 ),
    inference(avatar_split_clause,[],[f3067,f3069,f3053])).

fof(f3067,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_orders_2(sK1,X6,sK9(sK1,X7,X8,X6))
      | ~ r1_orders_2(sK1,X8,X6)
      | ~ r1_orders_2(sK1,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | k10_lattice3(sK1,X7,X8) = X6
      | v2_struct_0(sK1) ) ),
    inference(global_subsumption,[],[f2952,f3066])).

fof(f3066,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_orders_2(sK1,X6,sK9(sK1,X7,X8,X6))
      | ~ r1_orders_2(sK1,X8,X6)
      | ~ r1_orders_2(sK1,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X7,X8) = X6
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3041,f2950])).

fof(f3041,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_orders_2(sK1,X6,sK9(sK1,X7,X8,X6))
      | ~ r1_orders_2(sK1,X8,X6)
      | ~ r1_orders_2(sK1,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ m1_subset_1(X8,u1_struct_0(sK1))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X7,X8) = X6
      | ~ v5_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f2951,f2981])).

fof(f2981,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK9(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2925])).

fof(f3065,plain,
    ( spl20_1
    | spl20_3 ),
    inference(avatar_split_clause,[],[f3061,f3063,f3053])).

fof(f3061,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(sK1,X3,sK9(sK1,X4,X3,X5))
      | ~ r1_orders_2(sK1,X3,X5)
      | ~ r1_orders_2(sK1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | k10_lattice3(sK1,X4,X3) = X5
      | v2_struct_0(sK1) ) ),
    inference(global_subsumption,[],[f2952,f3060])).

fof(f3060,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(sK1,X3,sK9(sK1,X4,X3,X5))
      | ~ r1_orders_2(sK1,X3,X5)
      | ~ r1_orders_2(sK1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X4,X3) = X5
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3040,f2950])).

fof(f3040,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(sK1,X3,sK9(sK1,X4,X3,X5))
      | ~ r1_orders_2(sK1,X3,X5)
      | ~ r1_orders_2(sK1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X4,X3) = X5
      | ~ v5_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f2951,f2980])).

fof(f2980,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_lattice3(X0)
      | r1_orders_2(X0,X2,sK9(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2925])).

fof(f3059,plain,
    ( spl20_1
    | spl20_2 ),
    inference(avatar_split_clause,[],[f3051,f3057,f3053])).

fof(f3051,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK1,X0,sK9(sK1,X0,X1,X2))
      | ~ r1_orders_2(sK1,X1,X2)
      | ~ r1_orders_2(sK1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k10_lattice3(sK1,X0,X1) = X2
      | v2_struct_0(sK1) ) ),
    inference(global_subsumption,[],[f2952,f3050])).

fof(f3050,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK1,X0,sK9(sK1,X0,X1,X2))
      | ~ r1_orders_2(sK1,X1,X2)
      | ~ r1_orders_2(sK1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X0,X1) = X2
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3039,f2950])).

fof(f3039,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK1,X0,sK9(sK1,X0,X1,X2))
      | ~ r1_orders_2(sK1,X1,X2)
      | ~ r1_orders_2(sK1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | k10_lattice3(sK1,X0,X1) = X2
      | ~ v5_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f2951,f2979])).

fof(f2979,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_lattice3(X0)
      | r1_orders_2(X0,X1,sK9(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2925])).
%------------------------------------------------------------------------------
