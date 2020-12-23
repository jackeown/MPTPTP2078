%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1485+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 6.13s
% Output     : Refutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 761 expanded)
%              Number of leaves         :   20 ( 284 expanded)
%              Depth                    :   22
%              Number of atoms          :  916 (5418 expanded)
%              Number of equality atoms :   91 ( 793 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10880,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3439,f3501,f4015,f9864,f9892,f10879])).

fof(f10879,plain,
    ( ~ spl22_23
    | ~ spl22_24
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(avatar_contradiction_clause,[],[f10878])).

fof(f10878,plain,
    ( $false
    | ~ spl22_23
    | ~ spl22_24
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(subsumption_resolution,[],[f10871,f2995])).

fof(f2995,plain,(
    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f2934])).

fof(f2934,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2875,f2933,f2932,f2931])).

fof(f2931,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2932,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2933,plain,
    ( ? [X2] :
        ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2875,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f2874])).

fof(f2874,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2856])).

fof(f2856,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2855])).

fof(f2855,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).

fof(f10871,plain,
    ( sK1 = k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl22_23
    | ~ spl22_24
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(backward_demodulation,[],[f3936,f10582])).

fof(f10582,plain,
    ( sK1 = k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl22_23
    | ~ spl22_24
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(subsumption_resolution,[],[f10556,f3437])).

fof(f3437,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl22_24 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3436,plain,
    ( spl22_24
  <=> m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_24])])).

fof(f10556,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 = k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl22_23
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(resolution,[],[f10482,f3434])).

fof(f3434,plain,
    ( r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl22_23 ),
    inference(avatar_component_clause,[],[f3432])).

fof(f3432,plain,
    ( spl22_23
  <=> r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_23])])).

fof(f10482,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = k11_lattice3(sK0,sK1,X0) )
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(subsumption_resolution,[],[f10478,f2993])).

fof(f2993,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2934])).

fof(f10478,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = k11_lattice3(sK0,sK1,X0) )
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(resolution,[],[f10417,f4008])).

fof(f4008,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X0)
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k11_lattice3(sK0,X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f4004])).

fof(f4004,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,X0,X1) = X0
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k11_lattice3(sK0,X0,X1) = X0 ) ),
    inference(resolution,[],[f3158,f3154])).

fof(f3154,plain,(
    ! [X10,X8,X9] :
      ( r1_orders_2(sK0,sK12(sK0,X8,X9,X10),X8)
      | ~ r1_orders_2(sK0,X10,X9)
      | ~ r1_orders_2(sK0,X10,X8)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k11_lattice3(sK0,X8,X9) = X10 ) ),
    inference(global_subsumption,[],[f2992,f3131,f3153])).

fof(f3153,plain,(
    ! [X10,X8,X9] :
      ( r1_orders_2(sK0,sK12(sK0,X8,X9,X10),X8)
      | ~ r1_orders_2(sK0,X10,X9)
      | ~ r1_orders_2(sK0,X10,X8)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k11_lattice3(sK0,X8,X9) = X10
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3136,f2989])).

fof(f2989,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2934])).

fof(f3136,plain,(
    ! [X10,X8,X9] :
      ( r1_orders_2(sK0,sK12(sK0,X8,X9,X10),X8)
      | ~ r1_orders_2(sK0,X10,X9)
      | ~ r1_orders_2(sK0,X10,X8)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k11_lattice3(sK0,X8,X9) = X10
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2991,f3043])).

fof(f3043,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | r1_orders_2(X0,sK12(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2967])).

fof(f2967,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK12(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK12(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK12(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK12(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f2965,f2966])).

fof(f2966,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK12(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK12(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK12(X0,X1,X2,X3),X1)
        & m1_subset_1(sK12(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2965,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2964])).

fof(f2964,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2963])).

fof(f2963,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2917])).

fof(f2917,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2916])).

fof(f2916,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2842])).

fof(f2842,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(f2991,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f2934])).

fof(f3131,plain,(
    ~ v2_struct_0(sK0) ),
    inference(global_subsumption,[],[f2992,f3098])).

fof(f3098,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f2990,f3077])).

fof(f3077,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2930])).

fof(f2930,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2929])).

fof(f2929,plain,(
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

fof(f2990,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f2934])).

fof(f2992,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2934])).

fof(f3158,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_orders_2(sK0,sK12(sK0,X14,X15,X16),X16)
      | ~ r1_orders_2(sK0,X16,X15)
      | ~ r1_orders_2(sK0,X16,X14)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | k11_lattice3(sK0,X14,X15) = X16 ) ),
    inference(global_subsumption,[],[f2992,f3131,f3157])).

fof(f3157,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_orders_2(sK0,sK12(sK0,X14,X15,X16),X16)
      | ~ r1_orders_2(sK0,X16,X15)
      | ~ r1_orders_2(sK0,X16,X14)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k11_lattice3(sK0,X14,X15) = X16
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3138,f2989])).

fof(f3138,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_orders_2(sK0,sK12(sK0,X14,X15,X16),X16)
      | ~ r1_orders_2(sK0,X16,X15)
      | ~ r1_orders_2(sK0,X16,X14)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k11_lattice3(sK0,X14,X15) = X16
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2991,f3045])).

fof(f3045,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r1_orders_2(X0,sK12(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2967])).

fof(f10417,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl22_35
    | ~ spl22_118 ),
    inference(backward_demodulation,[],[f9859,f10414])).

fof(f10414,plain,
    ( sK1 = k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1))
    | ~ spl22_35 ),
    inference(forward_demodulation,[],[f4061,f4209])).

fof(f4209,plain,(
    sK1 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f3542,f2993])).

fof(f3542,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,k12_lattice3(sK0,sK1,X0),X0) = X0 ) ),
    inference(resolution,[],[f3150,f2993])).

fof(f3150,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k13_lattice3(sK0,k12_lattice3(sK0,X5,X4),X4) = X4 ) ),
    inference(global_subsumption,[],[f2992,f3149])).

fof(f3149,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,k12_lattice3(sK0,X5,X4),X4) = X4 ) ),
    inference(subsumption_resolution,[],[f3148,f2988])).

fof(f2988,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2934])).

fof(f3148,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,k12_lattice3(sK0,X5,X4),X4) = X4
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3147,f2989])).

fof(f3147,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,k12_lattice3(sK0,X5,X4),X4) = X4
      | ~ v5_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3134,f2990])).

fof(f3134,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,k12_lattice3(sK0,X5,X4),X4) = X4
      | ~ v1_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f2991,f3017])).

fof(f3017,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2891])).

fof(f2891,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f2890])).

fof(f2890,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2854])).

fof(f2854,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

fof(f4061,plain,
    ( k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)) = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK1),sK1)
    | ~ spl22_35 ),
    inference(resolution,[],[f3986,f3345])).

fof(f3345,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,sK1,X0) = k13_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f3102,f2993])).

fof(f3102,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k13_lattice3(sK0,X3,X2) = k13_lattice3(sK0,X2,X3) ) ),
    inference(global_subsumption,[],[f2992,f3101])).

fof(f3101,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X3,X2) = k13_lattice3(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f3089,f2989])).

fof(f3089,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X3,X2) = k13_lattice3(sK0,X2,X3)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f2990,f3019])).

fof(f3019,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2895])).

fof(f2895,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f2894])).

fof(f2894,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2809])).

fof(f2809,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

fof(f3986,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl22_35 ),
    inference(avatar_component_clause,[],[f3985])).

fof(f3985,plain,
    ( spl22_35
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_35])])).

fof(f9859,plain,
    ( r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ spl22_118 ),
    inference(avatar_component_clause,[],[f9857])).

fof(f9857,plain,
    ( spl22_118
  <=> r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_118])])).

fof(f3936,plain,
    ( k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) = k11_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ spl22_24 ),
    inference(resolution,[],[f3461,f3437])).

fof(f3461,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK1,X0) = k11_lattice3(sK0,sK1,X0) ) ),
    inference(resolution,[],[f3144,f2993])).

fof(f3144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) ) ),
    inference(global_subsumption,[],[f2992,f3143])).

fof(f3143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3132,f2989])).

fof(f3132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f2991,f3014])).

fof(f3014,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2885])).

fof(f2885,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f2884])).

fof(f2884,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2844])).

fof(f2844,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f9892,plain,
    ( ~ spl22_35
    | spl22_119 ),
    inference(avatar_contradiction_clause,[],[f9891])).

fof(f9891,plain,
    ( $false
    | ~ spl22_35
    | spl22_119 ),
    inference(subsumption_resolution,[],[f9890,f2989])).

fof(f9890,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl22_35
    | spl22_119 ),
    inference(subsumption_resolution,[],[f9889,f2990])).

fof(f9889,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl22_35
    | spl22_119 ),
    inference(subsumption_resolution,[],[f9888,f2992])).

fof(f9888,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl22_35
    | spl22_119 ),
    inference(subsumption_resolution,[],[f9887,f2993])).

fof(f9887,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl22_35
    | spl22_119 ),
    inference(subsumption_resolution,[],[f9886,f3986])).

fof(f9886,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_119 ),
    inference(resolution,[],[f9863,f3020])).

fof(f3020,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2897])).

fof(f2897,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f2896])).

fof(f2896,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2826])).

fof(f2826,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f9863,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | spl22_119 ),
    inference(avatar_component_clause,[],[f9861])).

fof(f9861,plain,
    ( spl22_119
  <=> m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_119])])).

fof(f9864,plain,
    ( spl22_118
    | ~ spl22_119
    | ~ spl22_35 ),
    inference(avatar_split_clause,[],[f9855,f3985,f9861,f9857])).

fof(f9855,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9854,f3131])).

fof(f9854,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9853,f2989])).

fof(f9853,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9852,f2990])).

fof(f9852,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9851,f2992])).

fof(f9851,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9850,f2993])).

fof(f9850,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(subsumption_resolution,[],[f9847,f3986])).

fof(f9847,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl22_35 ),
    inference(superposition,[],[f3087,f4059])).

fof(f4059,plain,
    ( k13_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1)) = k10_lattice3(sK0,sK1,k12_lattice3(sK0,sK1,sK1))
    | ~ spl22_35 ),
    inference(resolution,[],[f3986,f3244])).

fof(f3244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,sK1,X0) = k10_lattice3(sK0,sK1,X0) ) ),
    inference(resolution,[],[f3100,f2993])).

fof(f3100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k13_lattice3(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) ) ),
    inference(global_subsumption,[],[f2992,f3099])).

fof(f3099,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3088,f2989])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | k13_lattice3(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f2990,f3018])).

fof(f3018,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2893])).

fof(f2893,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f2892])).

fof(f2892,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2845])).

fof(f2845,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f3087,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3060])).

fof(f3060,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2980])).

fof(f2980,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK17(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK17(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK17(X0,X1,X2,X3))
                        & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f2978,f2979])).

fof(f2979,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK17(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK17(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK17(X0,X1,X2,X3))
        & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2978,plain,(
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
    inference(rectify,[],[f2977])).

fof(f2977,plain,(
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
    inference(flattening,[],[f2976])).

fof(f2976,plain,(
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
    inference(nnf_transformation,[],[f2926])).

fof(f2926,plain,(
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
    inference(flattening,[],[f2925])).

fof(f2925,plain,(
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
    inference(ennf_transformation,[],[f2841])).

fof(f2841,axiom,(
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

fof(f4015,plain,(
    spl22_35 ),
    inference(avatar_contradiction_clause,[],[f4014])).

fof(f4014,plain,
    ( $false
    | spl22_35 ),
    inference(subsumption_resolution,[],[f4013,f2989])).

fof(f4013,plain,
    ( ~ v5_orders_2(sK0)
    | spl22_35 ),
    inference(subsumption_resolution,[],[f4012,f2991])).

fof(f4012,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_35 ),
    inference(subsumption_resolution,[],[f4011,f2992])).

fof(f4011,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_35 ),
    inference(subsumption_resolution,[],[f4010,f2993])).

fof(f4010,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_35 ),
    inference(duplicate_literal_removal,[],[f4009])).

fof(f4009,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_35 ),
    inference(resolution,[],[f3987,f3016])).

fof(f3016,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2889])).

fof(f2889,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f2888])).

fof(f2888,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2825])).

fof(f2825,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f3987,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl22_35 ),
    inference(avatar_component_clause,[],[f3985])).

fof(f3501,plain,(
    spl22_24 ),
    inference(avatar_contradiction_clause,[],[f3500])).

fof(f3500,plain,
    ( $false
    | spl22_24 ),
    inference(subsumption_resolution,[],[f3499,f2989])).

fof(f3499,plain,
    ( ~ v5_orders_2(sK0)
    | spl22_24 ),
    inference(subsumption_resolution,[],[f3498,f2990])).

fof(f3498,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_24 ),
    inference(subsumption_resolution,[],[f3497,f2992])).

fof(f3497,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_24 ),
    inference(subsumption_resolution,[],[f3496,f2993])).

fof(f3496,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_24 ),
    inference(subsumption_resolution,[],[f3495,f2994])).

fof(f2994,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2934])).

fof(f3495,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl22_24 ),
    inference(resolution,[],[f3438,f3020])).

fof(f3438,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl22_24 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3439,plain,
    ( spl22_23
    | ~ spl22_24 ),
    inference(avatar_split_clause,[],[f3430,f3436,f3432])).

fof(f3430,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3429,f3131])).

fof(f3429,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3428,f2989])).

fof(f3428,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3427,f2990])).

fof(f3427,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3426,f2992])).

fof(f3426,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3425,f2993])).

fof(f3425,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3422,f2994])).

fof(f3422,plain,
    ( ~ m1_subset_1(k13_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f3087,f3278])).

fof(f3278,plain,(
    k13_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f3244,f2994])).
%------------------------------------------------------------------------------
