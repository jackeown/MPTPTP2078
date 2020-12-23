%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 388 expanded)
%              Number of leaves         :   27 ( 133 expanded)
%              Depth                    :   21
%              Number of atoms          :  858 (2643 expanded)
%              Number of equality atoms :   59 ( 334 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f151,f405,f468,f496])).

fof(f496,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | spl6_10 ),
    inference(subsumption_resolution,[],[f494,f72])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f50,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
    ( ? [X2] :
        ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f494,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f493,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f493,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f488,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f488,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl6_10 ),
    inference(resolution,[],[f401,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f401,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl6_10
  <=> m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f468,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f466,f69])).

fof(f69,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f466,plain,
    ( ~ v5_orders_2(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f465,f70])).

fof(f70,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f465,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f464,f72])).

fof(f464,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f463,f73])).

fof(f463,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl6_11 ),
    inference(subsumption_resolution,[],[f458,f74])).

fof(f458,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl6_11 ),
    inference(resolution,[],[f404,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f121,f108])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f404,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl6_11
  <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f405,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f398,f136,f403,f400])).

fof(f136,plain,
    ( spl6_1
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f398,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f397,f69])).

fof(f397,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f396,f71])).

fof(f71,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f396,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f395,f72])).

fof(f395,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f394,f73])).

fof(f394,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f377,f190])).

fof(f190,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f189,f68])).

fof(f68,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f189,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f188,f73])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f185,f72])).

fof(f185,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f179,f137])).

fof(f137,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X0)
      | ~ v3_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X0)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f165,f80])).

fof(f80,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_relat_2(u1_orders_2(X3),X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X4,X5)
      | r1_orders_2(X3,X4,X4) ) ),
    inference(subsumption_resolution,[],[f163,f154])).

fof(f154,plain,(
    ! [X0] :
      ( v1_relat_1(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f152,f103])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f152,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))) ) ),
    inference(resolution,[],[f77,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(X3,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X4,X5)
      | ~ r1_relat_2(u1_orders_2(X3),X5)
      | ~ v1_relat_1(u1_orders_2(X3)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(X3,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X4,X5)
      | ~ r1_relat_2(u1_orders_2(X3),X5)
      | ~ v1_relat_1(u1_orders_2(X3)) ) ),
    inference(resolution,[],[f83,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X3),X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f377,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( sK1 != sK1
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f171,f307])).

fof(f307,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(superposition,[],[f204,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

% (9772)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (9777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (9774)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (9780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (9776)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (9769)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (9785)Refutation not found, incomplete strategy% (9785)------------------------------
% (9785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9785)Termination reason: Refutation not found, incomplete strategy

% (9785)Memory used [KB]: 10618
% (9785)Time elapsed: 0.116 s
% (9785)------------------------------
% (9785)------------------------------
fof(f203,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f124,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f102,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).

fof(f66,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f100,f79])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f171,plain,(
    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f170,f69])).

fof(f170,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f169,f70])).

fof(f169,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f168,f72])).

fof(f168,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f167,f73])).

fof(f167,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f166,f74])).

fof(f166,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f75,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f75,plain,(
    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f151,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f149,f131])).

fof(f131,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f72])).

fof(f130,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f78,f70])).

fof(f149,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f148,f129])).

fof(f129,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f76,f72])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f148,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f140,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f140,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f141,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f133,f139,f136])).

fof(f133,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f104,f73])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (9779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (9773)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (9770)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (9766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9766)Refutation not found, incomplete strategy% (9766)------------------------------
% 0.20/0.48  % (9766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9766)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9766)Memory used [KB]: 10618
% 0.20/0.48  % (9766)Time elapsed: 0.062 s
% 0.20/0.48  % (9766)------------------------------
% 0.20/0.48  % (9766)------------------------------
% 0.20/0.48  % (9768)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (9778)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (9785)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (9781)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (9771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (9782)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (9765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (9767)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (9784)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (9783)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (9775)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (9767)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f497,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f141,f151,f405,f468,f496])).
% 0.20/0.51  fof(f496,plain,(
% 0.20/0.51    spl6_10),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f495])).
% 0.20/0.51  fof(f495,plain,(
% 0.20/0.51    $false | spl6_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f494,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    l1_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ((sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f50,f49,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ? [X2] : (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).
% 0.20/0.51  fof(f494,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | spl6_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f493,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f493,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl6_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f488,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f488,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl6_10),
% 0.20/0.51    inference(resolution,[],[f401,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.20/0.51  fof(f401,plain,(
% 0.20/0.51    ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl6_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f400])).
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    spl6_10 <=> m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f468,plain,(
% 0.20/0.51    spl6_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f467])).
% 0.20/0.51  fof(f467,plain,(
% 0.20/0.51    $false | spl6_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f466,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    v5_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f466,plain,(
% 0.20/0.51    ~v5_orders_2(sK0) | spl6_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f465,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    v1_lattice3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl6_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f464,f72])).
% 0.20/0.51  fof(f464,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl6_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f463,f73])).
% 0.20/0.51  fof(f463,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl6_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f458,f74])).
% 0.20/0.51  fof(f458,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl6_11),
% 0.20/0.51    inference(resolution,[],[f404,f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f176])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(resolution,[],[f121,f108])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK4(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3)) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK4(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3)) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(rectify,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.20/0.51  fof(f404,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | spl6_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f403])).
% 0.20/0.51  fof(f403,plain,(
% 0.20/0.51    spl6_11 <=> r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    ~spl6_10 | ~spl6_11 | ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f398,f136,f403,f400])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl6_1 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f398,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f397,f69])).
% 0.20/0.51  fof(f397,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f396,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    v2_lattice3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f395,f72])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f394,f73])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f377,f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    r1_orders_2(sK0,sK1,sK1) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f189,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    v3_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f188,f73])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f72])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | ~spl6_1),
% 0.20/0.51    inference(resolution,[],[f179,f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r1_orders_2(X1,X0,X0) | ~v3_orders_2(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_hidden(X0,u1_struct_0(X1)) | r1_orders_2(X1,X0,X0) | ~v3_orders_2(X1) | ~l1_orders_2(X1)) )),
% 0.20/0.51    inference(resolution,[],[f165,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0] : (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ! [X0] : (((v3_orders_2(X0) | ~r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v3_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : ((v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => (v3_orders_2(X0) <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X4,X5,X3] : (~r1_relat_2(u1_orders_2(X3),X5) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r2_hidden(X4,X5) | r1_orders_2(X3,X4,X4)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f163,f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f152,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )),
% 0.20/0.51    inference(resolution,[],[f77,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X4,X5,X3] : (r1_orders_2(X3,X4,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r2_hidden(X4,X5) | ~r1_relat_2(u1_orders_2(X3),X5) | ~v1_relat_1(u1_orders_2(X3))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X4,X5,X3] : (r1_orders_2(X3,X4,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r2_hidden(X4,X5) | ~r1_relat_2(u1_orders_2(X3),X5) | ~v1_relat_1(u1_orders_2(X3))) )),
% 0.20/0.51    inference(resolution,[],[f83,f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1) | ~r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.20/0.51  fof(f377,plain,(
% 0.20/0.51    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f364])).
% 0.20/0.51  fof(f364,plain,(
% 0.20/0.51    sK1 != sK1 | ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.51    inference(superposition,[],[f171,f307])).
% 0.20/0.51  fof(f307,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (k12_lattice3(X6,X7,X8) = X7 | ~r1_orders_2(X6,X7,X8) | ~r1_orders_2(X6,X7,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f296])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ( ! [X6,X8,X7] : (k12_lattice3(X6,X7,X8) = X7 | ~r1_orders_2(X6,X7,X8) | ~r1_orders_2(X6,X7,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6)) )),
% 0.20/0.51    inference(superposition,[],[f204,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f203])).
% 0.20/0.51  % (9772)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (9777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (9774)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (9780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (9776)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (9769)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.33/0.52  % (9785)Refutation not found, incomplete strategy% (9785)------------------------------
% 1.33/0.52  % (9785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.52  % (9785)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.52  
% 1.33/0.52  % (9785)Memory used [KB]: 10618
% 1.33/0.52  % (9785)Time elapsed: 0.116 s
% 1.33/0.52  % (9785)------------------------------
% 1.33/0.52  % (9785)------------------------------
% 1.33/0.53  fof(f203,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.33/0.53    inference(resolution,[],[f124,f122])).
% 1.33/0.53  fof(f122,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f102,f79])).
% 1.33/0.53  fof(f79,plain,(
% 1.33/0.53    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.33/0.53    inference(flattening,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f11])).
% 1.33/0.53  fof(f11,axiom,(
% 1.33/0.53    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 1.33/0.53  fof(f102,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK5(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f67])).
% 1.33/0.53  fof(f67,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK5(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).
% 1.33/0.53  fof(f66,plain,(
% 1.33/0.53    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(rectify,[],[f64])).
% 1.33/0.53  fof(f64,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(flattening,[],[f63])).
% 1.33/0.53  fof(f63,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(nnf_transformation,[],[f37])).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(flattening,[],[f36])).
% 1.33/0.53  fof(f36,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f15])).
% 1.33/0.53  fof(f15,axiom,(
% 1.33/0.53    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 1.33/0.53  fof(f124,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK5(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f100,f79])).
% 1.33/0.53  fof(f100,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK5(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f67])).
% 1.33/0.53  fof(f171,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))),
% 1.33/0.53    inference(subsumption_resolution,[],[f170,f69])).
% 1.33/0.53  fof(f170,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~v5_orders_2(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f169,f70])).
% 1.33/0.53  fof(f169,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f168,f72])).
% 1.33/0.53  fof(f168,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f167,f73])).
% 1.33/0.53  fof(f167,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f166,f74])).
% 1.33/0.53  fof(f166,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.33/0.53    inference(superposition,[],[f75,f105])).
% 1.33/0.53  fof(f105,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f41])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.33/0.53    inference(flattening,[],[f40])).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f17])).
% 1.33/0.53  fof(f17,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 1.33/0.53  fof(f75,plain,(
% 1.33/0.53    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 1.33/0.53    inference(cnf_transformation,[],[f51])).
% 1.33/0.53  fof(f151,plain,(
% 1.33/0.53    ~spl6_2),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f150])).
% 1.33/0.53  fof(f150,plain,(
% 1.33/0.53    $false | ~spl6_2),
% 1.33/0.53    inference(subsumption_resolution,[],[f149,f131])).
% 1.33/0.53  fof(f131,plain,(
% 1.33/0.53    ~v2_struct_0(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f130,f72])).
% 1.33/0.53  fof(f130,plain,(
% 1.33/0.53    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 1.33/0.53    inference(resolution,[],[f78,f70])).
% 1.33/0.53  fof(f149,plain,(
% 1.33/0.53    v2_struct_0(sK0) | ~spl6_2),
% 1.33/0.53    inference(subsumption_resolution,[],[f148,f129])).
% 1.33/0.53  fof(f129,plain,(
% 1.33/0.53    l1_struct_0(sK0)),
% 1.33/0.53    inference(resolution,[],[f76,f72])).
% 1.33/0.53  fof(f76,plain,(
% 1.33/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.33/0.53  fof(f148,plain,(
% 1.33/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_2),
% 1.33/0.53    inference(resolution,[],[f140,f88])).
% 1.33/0.53  fof(f88,plain,(
% 1.33/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f33])).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(flattening,[],[f32])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.33/0.53  fof(f140,plain,(
% 1.33/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_2),
% 1.33/0.53    inference(avatar_component_clause,[],[f139])).
% 1.33/0.53  fof(f139,plain,(
% 1.33/0.53    spl6_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.33/0.53  fof(f141,plain,(
% 1.33/0.53    spl6_1 | spl6_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f133,f139,f136])).
% 1.33/0.53  fof(f133,plain,(
% 1.33/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 1.33/0.53    inference(resolution,[],[f104,f73])).
% 1.33/0.53  fof(f104,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f39])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.33/0.53    inference(flattening,[],[f38])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (9767)------------------------------
% 1.33/0.53  % (9767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (9767)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (9767)Memory used [KB]: 10874
% 1.33/0.53  % (9767)Time elapsed: 0.103 s
% 1.33/0.53  % (9767)------------------------------
% 1.33/0.53  % (9767)------------------------------
% 1.33/0.53  % (9759)Success in time 0.173 s
%------------------------------------------------------------------------------
