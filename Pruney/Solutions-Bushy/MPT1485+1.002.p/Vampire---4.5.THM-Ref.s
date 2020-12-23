%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1485+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:58 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 408 expanded)
%              Number of leaves         :   21 ( 149 expanded)
%              Depth                    :   21
%              Number of atoms          :  849 (2971 expanded)
%              Number of equality atoms :   60 ( 383 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f793,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f120,f132,f627,f749,f792])).

fof(f792,plain,(
    spl7_24 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | spl7_24 ),
    inference(subsumption_resolution,[],[f790,f56])).

fof(f56,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k13_lattice3(sK1,sK2,sK3))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1)
    & v3_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f37,f36,f35])).

fof(f35,plain,
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
              ( k12_lattice3(sK1,X1,k13_lattice3(sK1,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1)
      & v3_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k12_lattice3(sK1,X1,k13_lattice3(sK1,X1,X2)) != X1
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( sK2 != k12_lattice3(sK1,sK2,k13_lattice3(sK1,sK2,X2))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( sK2 != k12_lattice3(sK1,sK2,k13_lattice3(sK1,sK2,X2))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( sK2 != k12_lattice3(sK1,sK2,k13_lattice3(sK1,sK2,sK3))
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f790,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_24 ),
    inference(subsumption_resolution,[],[f789,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f789,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_24 ),
    inference(subsumption_resolution,[],[f784,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f784,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_24 ),
    inference(resolution,[],[f623,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f623,plain,
    ( ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f622])).

fof(f622,plain,
    ( spl7_24
  <=> m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f749,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | spl7_25 ),
    inference(subsumption_resolution,[],[f747,f56])).

fof(f747,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f746,f55])).

fof(f55,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f746,plain,
    ( ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | spl7_25 ),
    inference(resolution,[],[f731,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f731,plain,
    ( v2_struct_0(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f730,f53])).

fof(f53,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f730,plain,
    ( ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f729,f54])).

fof(f54,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f729,plain,
    ( ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f728,f56])).

fof(f728,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f727,f57])).

fof(f727,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f722,f58])).

fof(f722,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl7_25 ),
    inference(resolution,[],[f626,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f91,f85])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f626,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl7_25
  <=> r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f627,plain,
    ( ~ spl7_24
    | ~ spl7_25
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f620,f118,f625,f622])).

fof(f118,plain,
    ( spl7_3
  <=> r1_orders_2(sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f620,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f619,f53])).

fof(f619,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ v5_orders_2(sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f618,f55])).

fof(f618,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f617,f56])).

fof(f617,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f616,f57])).

fof(f616,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f599,f119])).

fof(f119,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f599,plain,
    ( ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(trivial_inequality_removal,[],[f586])).

fof(f586,plain,
    ( sK2 != sK2
    | ~ r1_orders_2(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k10_lattice3(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(superposition,[],[f126,f252])).

fof(f252,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(subsumption_resolution,[],[f250,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | sP0(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f44])).

fof(f44,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_lattice3)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f250,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ sP0(X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ sP0(X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(superposition,[],[f153,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP0(X0,X2,X1)
      | k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f67,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f126,plain,(
    sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f125,f53])).

fof(f125,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ v5_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f124,f54])).

fof(f124,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f123,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f122,f57])).

fof(f122,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f121,f58])).

fof(f121,plain,
    ( sK2 != k12_lattice3(sK1,sK2,k10_lattice3(sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(superposition,[],[f59,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f59,plain,(
    sK2 != k12_lattice3(sK1,sK2,k13_lattice3(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f130,f56])).

fof(f130,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f129,f55])).

fof(f129,plain,
    ( ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f100,f60])).

fof(f100,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( spl7_1
    | spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f116,f102,f118,f99])).

fof(f102,plain,
    ( spl7_2
  <=> ! [X0] :
        ( r3_orders_2(sK1,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f116,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f52,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f114,f56])).

fof(f114,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f113,f57])).

fof(f113,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( r1_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f108,plain,
    ( r3_orders_2(sK1,sK2,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f103,f57])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r3_orders_2(sK1,X0,X0) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f107,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f106,f102,f99])).

fof(f106,plain,(
    ! [X1] :
      ( r3_orders_2(sK1,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,(
    ! [X1] :
      ( r3_orders_2(sK1,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,(
    ! [X1] :
      ( r3_orders_2(sK1,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

%------------------------------------------------------------------------------
