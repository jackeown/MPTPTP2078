%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:35 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 459 expanded)
%              Number of leaves         :   24 ( 162 expanded)
%              Depth                    :   21
%              Number of atoms          :  807 (2996 expanded)
%              Number of equality atoms :   69 ( 399 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f204,f577,f615,f641])).

fof(f641,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | spl11_9 ),
    inference(subsumption_resolution,[],[f639,f73])).

fof(f73,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8))
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l1_orders_2(sK6)
    & v2_lattice3(sK6)
    & v1_lattice3(sK6)
    & v5_orders_2(sK6)
    & v3_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f15,f48,f47,f46])).

fof(f46,plain,
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
              ( k12_lattice3(sK6,X1,k13_lattice3(sK6,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK6)) )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l1_orders_2(sK6)
      & v2_lattice3(sK6)
      & v1_lattice3(sK6)
      & v5_orders_2(sK6)
      & v3_orders_2(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k12_lattice3(sK6,X1,k13_lattice3(sK6,X1,X2)) != X1
            & m1_subset_1(X2,u1_struct_0(sK6)) )
        & m1_subset_1(X1,u1_struct_0(sK6)) )
   => ( ? [X2] :
          ( sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,X2))
          & m1_subset_1(X2,u1_struct_0(sK6)) )
      & m1_subset_1(sK7,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,X2))
        & m1_subset_1(X2,u1_struct_0(sK6)) )
   => ( sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8))
      & m1_subset_1(sK8,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f639,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_9 ),
    inference(subsumption_resolution,[],[f638,f74])).

fof(f74,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f638,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_9 ),
    inference(subsumption_resolution,[],[f637,f69])).

fof(f69,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f637,plain,
    ( ~ v5_orders_2(sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_9 ),
    inference(subsumption_resolution,[],[f636,f70])).

fof(f70,plain,(
    v1_lattice3(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f636,plain,
    ( ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_9 ),
    inference(subsumption_resolution,[],[f634,f72])).

fof(f72,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f634,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | spl11_9 ),
    inference(resolution,[],[f587,f253])).

fof(f253,plain,(
    ! [X6,X8,X7] :
      ( r1_orders_2(X7,X6,k10_lattice3(X7,X6,X8))
      | ~ l1_orders_2(X7)
      | ~ v1_lattice3(X7)
      | ~ v5_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X6,u1_struct_0(X7)) ) ),
    inference(resolution,[],[f242,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ~ sP0(X3,X2,X1,X0)
        | ~ r1_orders_2(X2,X1,X3)
        | ~ r1_orders_2(X2,X0,X3) )
      & ( ( sP0(X3,X2,X1,X0)
          & r1_orders_2(X2,X1,X3)
          & r1_orders_2(X2,X0,X3) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP1(X1,X2,X0,X3)
        | ~ sP0(X3,X0,X2,X1)
        | ~ r1_orders_2(X0,X2,X3)
        | ~ r1_orders_2(X0,X1,X3) )
      & ( ( sP0(X3,X0,X2,X1)
          & r1_orders_2(X0,X2,X3)
          & r1_orders_2(X0,X1,X3) )
        | ~ sP1(X1,X2,X0,X3) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP1(X1,X2,X0,X3)
        | ~ sP0(X3,X0,X2,X1)
        | ~ r1_orders_2(X0,X2,X3)
        | ~ r1_orders_2(X0,X1,X3) )
      & ( ( sP0(X3,X0,X2,X1)
          & r1_orders_2(X0,X2,X3)
          & r1_orders_2(X0,X1,X3) )
        | ~ sP1(X1,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0,X3] :
      ( sP1(X1,X2,X0,X3)
    <=> ( sP0(X3,X0,X2,X1)
        & r1_orders_2(X0,X2,X3)
        & r1_orders_2(X0,X1,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X2,X0,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f240,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP1(X1,X2,X0,k10_lattice3(X0,X1,X2)) ) ),
    inference(resolution,[],[f217,f109])).

fof(f109,plain,(
    ! [X2,X3,X1] :
      ( ~ sP2(k10_lattice3(X1,X3,X2),X1,X2,X3)
      | sP1(X3,X2,X1,k10_lattice3(X1,X3,X2)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X3,X2,X1,X0)
      | k10_lattice3(X1,X3,X2) != X0
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k10_lattice3(X1,X3,X2) = X0
          | ~ sP1(X3,X2,X1,X0) )
        & ( sP1(X3,X2,X1,X0)
          | k10_lattice3(X1,X3,X2) != X0 ) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( k10_lattice3(X0,X1,X2) = X3
          | ~ sP1(X1,X2,X0,X3) )
        & ( sP1(X1,X2,X0,X3)
          | k10_lattice3(X0,X1,X2) != X3 ) )
      | ~ sP2(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X3,X0,X2,X1] :
      ( ( k10_lattice3(X0,X1,X2) = X3
      <=> sP1(X1,X2,X0,X3) )
      | ~ sP2(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f89,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP2(X3,X0,X2,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f40,f39,f38])).

fof(f38,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ! [X4] :
          ( r1_orders_2(X0,X3,X4)
          | ~ r1_orders_2(X0,X2,X4)
          | ~ r1_orders_2(X0,X1,X4)
          | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f587,plain,
    ( ~ r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | spl11_9 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl11_9
  <=> r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f615,plain,
    ( ~ spl11_5
    | ~ spl11_9
    | ~ spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f614,f188,f184,f585,f316])).

fof(f316,plain,
    ( spl11_5
  <=> r1_orders_2(sK6,sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f184,plain,
    ( spl11_3
  <=> m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f188,plain,
    ( spl11_4
  <=> sK7 = k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f614,plain,
    ( ~ r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ r1_orders_2(sK6,sK7,sK7)
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f350,f73])).

fof(f350,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ r1_orders_2(sK6,sK7,sK7)
    | ~ spl11_3
    | spl11_4 ),
    inference(trivial_inequality_removal,[],[f348])).

fof(f348,plain,
    ( sK7 != sK7
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ r1_orders_2(sK6,sK7,sK7)
    | ~ spl11_3
    | spl11_4 ),
    inference(resolution,[],[f304,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,X0) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2,X0)
      | sP3(X0,X1,X2,X0) ) ),
    inference(resolution,[],[f100,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK10(X0,X1,X2,X3),X3)
      | sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ~ r1_orders_2(X1,sK10(X0,X1,X2,X3),X0)
          & r1_orders_2(X1,sK10(X0,X1,X2,X3),X2)
          & r1_orders_2(X1,sK10(X0,X1,X2,X3),X3)
          & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r1_orders_2(X1,X5,X0)
            | ~ r1_orders_2(X1,X5,X2)
            | ~ r1_orders_2(X1,X5,X3)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f65,f66])).

fof(f66,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK10(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK10(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK10(X0,X1,X2,X3),X3)
        & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r1_orders_2(X1,X4,X0)
            & r1_orders_2(X1,X4,X2)
            & r1_orders_2(X1,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r1_orders_2(X1,X5,X0)
            | ~ r1_orders_2(X1,X5,X2)
            | ~ r1_orders_2(X1,X5,X3)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP3(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r1_orders_2(X0,X4,X3)
            & r1_orders_2(X0,X4,X2)
            & r1_orders_2(X0,X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X0,X4,X3)
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r1_orders_2(X0,X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP3(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X3,X0,X2,X1] :
      ( sP3(X3,X0,X2,X1)
    <=> ! [X4] :
          ( r1_orders_2(X0,X4,X3)
          | ~ r1_orders_2(X0,X4,X2)
          | ~ r1_orders_2(X0,X4,X1)
          | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK10(X0,X1,X2,X3),X0)
      | sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK6,k10_lattice3(sK6,sK7,sK8),sK7)
        | sK7 != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r1_orders_2(sK6,X0,k10_lattice3(sK6,sK7,sK8))
        | ~ r1_orders_2(sK6,X0,sK7) )
    | ~ spl11_3
    | spl11_4 ),
    inference(resolution,[],[f280,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | ~ sP3(X3,X2,X1,X0)
      | ~ r1_orders_2(X2,X3,X1)
      | ~ r1_orders_2(X2,X3,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ~ sP3(X3,X2,X1,X0)
        | ~ r1_orders_2(X2,X3,X1)
        | ~ r1_orders_2(X2,X3,X0) )
      & ( ( sP3(X3,X2,X1,X0)
          & r1_orders_2(X2,X3,X1)
          & r1_orders_2(X2,X3,X0) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP4(X1,X2,X0,X3)
        | ~ sP3(X3,X0,X2,X1)
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( sP3(X3,X0,X2,X1)
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP4(X1,X2,X0,X3) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP4(X1,X2,X0,X3)
        | ~ sP3(X3,X0,X2,X1)
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( sP3(X3,X0,X2,X1)
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP4(X1,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0,X3] :
      ( sP4(X1,X2,X0,X3)
    <=> ( sP3(X3,X0,X2,X1)
        & r1_orders_2(X0,X3,X2)
        & r1_orders_2(X0,X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f280,plain,
    ( ! [X4] :
        ( ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK6))
        | sK7 != X4 )
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f279,f69])).

fof(f279,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK6))
        | ~ v5_orders_2(sK6)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | sK7 != X4 )
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f278,f71])).

fof(f71,plain,(
    v2_lattice3(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f278,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK6))
        | ~ v2_lattice3(sK6)
        | ~ v5_orders_2(sK6)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | sK7 != X4 )
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f277,f72])).

fof(f277,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK6))
        | ~ l1_orders_2(sK6)
        | ~ v2_lattice3(sK6)
        | ~ v5_orders_2(sK6)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | sK7 != X4 )
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f276,f73])).

fof(f276,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK6))
        | ~ m1_subset_1(sK7,u1_struct_0(sK6))
        | ~ l1_orders_2(sK6)
        | ~ v2_lattice3(sK6)
        | ~ v5_orders_2(sK6)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | sK7 != X4 )
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f267,f185])).

fof(f185,plain,
    ( m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f267,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK6))
        | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
        | ~ m1_subset_1(sK7,u1_struct_0(sK6))
        | ~ l1_orders_2(sK6)
        | ~ v2_lattice3(sK6)
        | ~ v5_orders_2(sK6)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4)
        | sK7 != X4 )
    | spl11_4 ),
    inference(resolution,[],[f250,f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ sP5(X0,sK6,k10_lattice3(sK6,sK7,sK8),sK7)
        | ~ sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X0)
        | sK7 != X0 )
    | spl11_4 ),
    inference(superposition,[],[f190,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X1,X3,X2) = X0
      | ~ sP4(X3,X2,X1,X0)
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k11_lattice3(X1,X3,X2) = X0
          | ~ sP4(X3,X2,X1,X0) )
        & ( sP4(X3,X2,X1,X0)
          | k11_lattice3(X1,X3,X2) != X0 ) )
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( k11_lattice3(X0,X1,X2) = X3
          | ~ sP4(X1,X2,X0,X3) )
        & ( sP4(X1,X2,X0,X3)
          | k11_lattice3(X0,X1,X2) != X3 ) )
      | ~ sP5(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X3,X0,X2,X1] :
      ( ( k11_lattice3(X0,X1,X2) = X3
      <=> sP4(X1,X2,X0,X3) )
      | ~ sP5(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f190,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f250,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f101,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP5(X3,X0,X2,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f44,f43,f42])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f577,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f575,f68])).

fof(f68,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f575,plain,
    ( ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f574,f71])).

fof(f574,plain,
    ( ~ v2_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f573,f69])).

fof(f573,plain,
    ( ~ v5_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f572,f70])).

fof(f572,plain,
    ( ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f571,f72])).

fof(f571,plain,
    ( ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f569,f73])).

fof(f569,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v3_orders_2(sK6)
    | spl11_5 ),
    inference(resolution,[],[f567,f318])).

fof(f318,plain,
    ( ~ r1_orders_2(sK6,sK7,sK7)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f316])).

fof(f567,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(condensation,[],[f566])).

fof(f566,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,X18,X18)
      | ~ l1_orders_2(X16)
      | ~ v1_lattice3(X16)
      | ~ v5_orders_2(X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ v2_lattice3(X16)
      | ~ v3_orders_2(X16) ) ),
    inference(subsumption_resolution,[],[f559,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f559,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,X18,X18)
      | ~ l1_orders_2(X16)
      | ~ v1_lattice3(X16)
      | ~ v5_orders_2(X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ v2_lattice3(X16)
      | ~ v3_orders_2(X16) ) ),
    inference(duplicate_literal_removal,[],[f556])).

fof(f556,plain,(
    ! [X17,X18,X16] :
      ( r1_orders_2(X16,X18,X18)
      | ~ l1_orders_2(X16)
      | ~ v1_lattice3(X16)
      | ~ v5_orders_2(X16)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ l1_orders_2(X16)
      | ~ v2_lattice3(X16)
      | ~ v1_lattice3(X16)
      | ~ v5_orders_2(X16)
      | ~ v3_orders_2(X16) ) ),
    inference(superposition,[],[f252,f534])).

fof(f534,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f531,f108])).

fof(f531,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ m1_subset_1(k11_lattice3(X3,X4,X5),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(k11_lattice3(X3,X4,X5),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f303,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k11_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k11_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f102,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f252,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(X4,X5,k10_lattice3(X4,X3,X5))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f242,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X2,X1,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f204,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl11_3 ),
    inference(subsumption_resolution,[],[f202,f72])).

fof(f202,plain,
    ( ~ l1_orders_2(sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f201,f73])).

fof(f201,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f199,f74])).

fof(f199,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | spl11_3 ),
    inference(resolution,[],[f186,f107])).

fof(f186,plain,
    ( ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f191,plain,
    ( ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f182,f188,f184])).

fof(f182,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f181,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f180,f71])).

fof(f180,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f179,f72])).

fof(f179,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f165,f73])).

fof(f165,plain,
    ( sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v2_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(superposition,[],[f162,f106])).

fof(f162,plain,(
    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) ),
    inference(subsumption_resolution,[],[f161,f69])).

fof(f161,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f160,f70])).

fof(f160,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f159,f72])).

fof(f159,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f158,f73])).

fof(f158,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(subsumption_resolution,[],[f157,f74])).

fof(f157,plain,
    ( sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6)
    | ~ v1_lattice3(sK6)
    | ~ v5_orders_2(sK6) ),
    inference(superposition,[],[f75,f105])).

fof(f75,plain,(
    sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:19 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.46  % (24174)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (24182)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (24162)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (24163)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (24169)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (24164)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (24185)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (24165)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (24170)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (24171)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (24179)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (24167)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (24166)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24177)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (24168)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (24176)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (24178)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (24186)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (24173)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (24172)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (24175)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (24180)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (24183)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (24181)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (24187)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.61/0.56  % (24184)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.61/0.56  % (24166)Refutation found. Thanks to Tanya!
% 1.61/0.56  % SZS status Theorem for theBenchmark
% 1.61/0.56  % SZS output start Proof for theBenchmark
% 1.61/0.56  fof(f644,plain,(
% 1.61/0.56    $false),
% 1.61/0.56    inference(avatar_sat_refutation,[],[f191,f204,f577,f615,f641])).
% 1.61/0.56  fof(f641,plain,(
% 1.61/0.56    spl11_9),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f640])).
% 1.61/0.56  fof(f640,plain,(
% 1.61/0.56    $false | spl11_9),
% 1.61/0.56    inference(subsumption_resolution,[],[f639,f73])).
% 1.61/0.56  fof(f73,plain,(
% 1.61/0.56    m1_subset_1(sK7,u1_struct_0(sK6))),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f49,plain,(
% 1.61/0.56    ((sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8)) & m1_subset_1(sK8,u1_struct_0(sK6))) & m1_subset_1(sK7,u1_struct_0(sK6))) & l1_orders_2(sK6) & v2_lattice3(sK6) & v1_lattice3(sK6) & v5_orders_2(sK6) & v3_orders_2(sK6)),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f15,f48,f47,f46])).
% 1.61/0.56  fof(f46,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK6,X1,k13_lattice3(sK6,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK6))) & m1_subset_1(X1,u1_struct_0(sK6))) & l1_orders_2(sK6) & v2_lattice3(sK6) & v1_lattice3(sK6) & v5_orders_2(sK6) & v3_orders_2(sK6))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f47,plain,(
% 1.61/0.56    ? [X1] : (? [X2] : (k12_lattice3(sK6,X1,k13_lattice3(sK6,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK6))) & m1_subset_1(X1,u1_struct_0(sK6))) => (? [X2] : (sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,X2)) & m1_subset_1(X2,u1_struct_0(sK6))) & m1_subset_1(sK7,u1_struct_0(sK6)))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f48,plain,(
% 1.61/0.56    ? [X2] : (sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,X2)) & m1_subset_1(X2,u1_struct_0(sK6))) => (sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8)) & m1_subset_1(sK8,u1_struct_0(sK6)))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f15,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f14])).
% 1.61/0.56  fof(f14,plain,(
% 1.61/0.56    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f13])).
% 1.61/0.56  fof(f13,negated_conjecture,(
% 1.61/0.56    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 1.61/0.56    inference(negated_conjecture,[],[f12])).
% 1.61/0.56  fof(f12,conjecture,(
% 1.61/0.56    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattice3)).
% 1.61/0.56  fof(f639,plain,(
% 1.61/0.56    ~m1_subset_1(sK7,u1_struct_0(sK6)) | spl11_9),
% 1.61/0.56    inference(subsumption_resolution,[],[f638,f74])).
% 1.61/0.56  fof(f74,plain,(
% 1.61/0.56    m1_subset_1(sK8,u1_struct_0(sK6))),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f638,plain,(
% 1.61/0.56    ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | spl11_9),
% 1.61/0.56    inference(subsumption_resolution,[],[f637,f69])).
% 1.61/0.56  fof(f69,plain,(
% 1.61/0.56    v5_orders_2(sK6)),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f637,plain,(
% 1.61/0.56    ~v5_orders_2(sK6) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | spl11_9),
% 1.61/0.56    inference(subsumption_resolution,[],[f636,f70])).
% 1.61/0.56  fof(f70,plain,(
% 1.61/0.56    v1_lattice3(sK6)),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f636,plain,(
% 1.61/0.56    ~v1_lattice3(sK6) | ~v5_orders_2(sK6) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | spl11_9),
% 1.61/0.56    inference(subsumption_resolution,[],[f634,f72])).
% 1.61/0.56  fof(f72,plain,(
% 1.61/0.56    l1_orders_2(sK6)),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f634,plain,(
% 1.61/0.56    ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | spl11_9),
% 1.61/0.56    inference(resolution,[],[f587,f253])).
% 1.61/0.56  fof(f253,plain,(
% 1.61/0.56    ( ! [X6,X8,X7] : (r1_orders_2(X7,X6,k10_lattice3(X7,X6,X8)) | ~l1_orders_2(X7) | ~v1_lattice3(X7) | ~v5_orders_2(X7) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X6,u1_struct_0(X7))) )),
% 1.61/0.56    inference(resolution,[],[f242,f80])).
% 1.61/0.56  fof(f80,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_orders_2(X2,X0,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f54])).
% 1.61/0.56  fof(f54,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ~sP0(X3,X2,X1,X0) | ~r1_orders_2(X2,X1,X3) | ~r1_orders_2(X2,X0,X3)) & ((sP0(X3,X2,X1,X0) & r1_orders_2(X2,X1,X3) & r1_orders_2(X2,X0,X3)) | ~sP1(X0,X1,X2,X3)))),
% 1.61/0.56    inference(rectify,[],[f53])).
% 1.61/0.56  fof(f53,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : ((sP1(X1,X2,X0,X3) | ~sP0(X3,X0,X2,X1) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((sP0(X3,X0,X2,X1) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~sP1(X1,X2,X0,X3)))),
% 1.61/0.56    inference(flattening,[],[f52])).
% 1.61/0.56  fof(f52,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : ((sP1(X1,X2,X0,X3) | (~sP0(X3,X0,X2,X1) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((sP0(X3,X0,X2,X1) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~sP1(X1,X2,X0,X3)))),
% 1.61/0.56    inference(nnf_transformation,[],[f39])).
% 1.61/0.56  fof(f39,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : (sP1(X1,X2,X0,X3) <=> (sP0(X3,X0,X2,X1) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.61/0.56  fof(f242,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (sP1(X1,X2,X0,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f240,f107])).
% 1.61/0.56  fof(f107,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f35])).
% 1.61/0.56  fof(f35,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f34])).
% 1.61/0.56  fof(f34,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f4])).
% 1.61/0.56  fof(f4,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 1.61/0.56  fof(f240,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | sP1(X1,X2,X0,k10_lattice3(X0,X1,X2))) )),
% 1.61/0.56    inference(resolution,[],[f217,f109])).
% 1.61/0.56  fof(f109,plain,(
% 1.61/0.56    ( ! [X2,X3,X1] : (~sP2(k10_lattice3(X1,X3,X2),X1,X2,X3) | sP1(X3,X2,X1,k10_lattice3(X1,X3,X2))) )),
% 1.61/0.56    inference(equality_resolution,[],[f78])).
% 1.61/0.56  fof(f78,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP1(X3,X2,X1,X0) | k10_lattice3(X1,X3,X2) != X0 | ~sP2(X0,X1,X2,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f51])).
% 1.61/0.56  fof(f51,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : (((k10_lattice3(X1,X3,X2) = X0 | ~sP1(X3,X2,X1,X0)) & (sP1(X3,X2,X1,X0) | k10_lattice3(X1,X3,X2) != X0)) | ~sP2(X0,X1,X2,X3))),
% 1.61/0.56    inference(rectify,[],[f50])).
% 1.61/0.56  fof(f50,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : (((k10_lattice3(X0,X1,X2) = X3 | ~sP1(X1,X2,X0,X3)) & (sP1(X1,X2,X0,X3) | k10_lattice3(X0,X1,X2) != X3)) | ~sP2(X3,X0,X2,X1))),
% 1.61/0.56    inference(nnf_transformation,[],[f40])).
% 1.61/0.56  fof(f40,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : ((k10_lattice3(X0,X1,X2) = X3 <=> sP1(X1,X2,X0,X3)) | ~sP2(X3,X0,X2,X1))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.61/0.56  fof(f217,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP2(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f89,f76])).
% 1.61/0.56  fof(f76,plain,(
% 1.61/0.56    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f17])).
% 1.61/0.56  fof(f17,plain,(
% 1.61/0.56    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f16])).
% 1.61/0.56  fof(f16,plain,(
% 1.61/0.56    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f2])).
% 1.61/0.56  fof(f2,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 1.61/0.56  fof(f89,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP2(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f41])).
% 1.61/0.56  fof(f41,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP2(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.56    inference(definition_folding,[],[f21,f40,f39,f38])).
% 1.61/0.56  fof(f38,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : (sP0(X3,X0,X2,X1) <=> ! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.61/0.56  fof(f21,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.56    inference(flattening,[],[f20])).
% 1.61/0.56  fof(f20,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f6])).
% 1.61/0.56  fof(f6,axiom,(
% 1.61/0.56    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 1.61/0.56  fof(f587,plain,(
% 1.61/0.56    ~r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | spl11_9),
% 1.61/0.56    inference(avatar_component_clause,[],[f585])).
% 1.61/0.56  fof(f585,plain,(
% 1.61/0.56    spl11_9 <=> r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.61/0.56  fof(f615,plain,(
% 1.61/0.56    ~spl11_5 | ~spl11_9 | ~spl11_3 | spl11_4),
% 1.61/0.56    inference(avatar_split_clause,[],[f614,f188,f184,f585,f316])).
% 1.61/0.56  fof(f316,plain,(
% 1.61/0.56    spl11_5 <=> r1_orders_2(sK6,sK7,sK7)),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.61/0.56  fof(f184,plain,(
% 1.61/0.56    spl11_3 <=> m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.61/0.56  fof(f188,plain,(
% 1.61/0.56    spl11_4 <=> sK7 = k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))),
% 1.61/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.61/0.56  fof(f614,plain,(
% 1.61/0.56    ~r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~r1_orders_2(sK6,sK7,sK7) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f350,f73])).
% 1.61/0.56  fof(f350,plain,(
% 1.61/0.56    ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~r1_orders_2(sK6,sK7,sK7) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(trivial_inequality_removal,[],[f348])).
% 1.61/0.56  fof(f348,plain,(
% 1.61/0.56    sK7 != sK7 | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~r1_orders_2(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~r1_orders_2(sK6,sK7,sK7) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(resolution,[],[f304,f120])).
% 1.61/0.56  fof(f120,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,X0)) )),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f117])).
% 1.61/0.56  fof(f117,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,X0) | sP3(X0,X1,X2,X0)) )),
% 1.61/0.56    inference(resolution,[],[f100,f98])).
% 1.61/0.56  fof(f98,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,sK10(X0,X1,X2,X3),X3) | sP3(X0,X1,X2,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f67])).
% 1.61/0.56  fof(f67,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (~r1_orders_2(X1,sK10(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK10(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK10(X0,X1,X2,X3),X3) & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X1)))) & (! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP3(X0,X1,X2,X3)))),
% 1.61/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f65,f66])).
% 1.61/0.56  fof(f66,plain,(
% 1.61/0.56    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) => (~r1_orders_2(X1,sK10(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK10(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK10(X0,X1,X2,X3),X3) & m1_subset_1(sK10(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.61/0.56    introduced(choice_axiom,[])).
% 1.61/0.56  fof(f65,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP3(X0,X1,X2,X3)))),
% 1.61/0.56    inference(rectify,[],[f64])).
% 1.61/0.56  fof(f64,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : ((sP3(X3,X0,X2,X1) | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP3(X3,X0,X2,X1)))),
% 1.61/0.56    inference(nnf_transformation,[],[f42])).
% 1.61/0.56  fof(f42,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : (sP3(X3,X0,X2,X1) <=> ! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.61/0.56  fof(f100,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X1,sK10(X0,X1,X2,X3),X0) | sP3(X0,X1,X2,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f67])).
% 1.61/0.56  fof(f304,plain,(
% 1.61/0.56    ( ! [X0] : (~sP3(X0,sK6,k10_lattice3(sK6,sK7,sK8),sK7) | sK7 != X0 | ~m1_subset_1(X0,u1_struct_0(sK6)) | ~r1_orders_2(sK6,X0,k10_lattice3(sK6,sK7,sK8)) | ~r1_orders_2(sK6,X0,sK7)) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(resolution,[],[f280,f95])).
% 1.61/0.56  fof(f95,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | ~sP3(X3,X2,X1,X0) | ~r1_orders_2(X2,X3,X1) | ~r1_orders_2(X2,X3,X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f63])).
% 1.61/0.56  fof(f63,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ~sP3(X3,X2,X1,X0) | ~r1_orders_2(X2,X3,X1) | ~r1_orders_2(X2,X3,X0)) & ((sP3(X3,X2,X1,X0) & r1_orders_2(X2,X3,X1) & r1_orders_2(X2,X3,X0)) | ~sP4(X0,X1,X2,X3)))),
% 1.61/0.56    inference(rectify,[],[f62])).
% 1.61/0.56  fof(f62,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : ((sP4(X1,X2,X0,X3) | ~sP3(X3,X0,X2,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((sP3(X3,X0,X2,X1) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP4(X1,X2,X0,X3)))),
% 1.61/0.56    inference(flattening,[],[f61])).
% 1.61/0.56  fof(f61,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : ((sP4(X1,X2,X0,X3) | (~sP3(X3,X0,X2,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((sP3(X3,X0,X2,X1) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP4(X1,X2,X0,X3)))),
% 1.61/0.56    inference(nnf_transformation,[],[f43])).
% 1.61/0.56  fof(f43,plain,(
% 1.61/0.56    ! [X1,X2,X0,X3] : (sP4(X1,X2,X0,X3) <=> (sP3(X3,X0,X2,X1) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.61/0.56  fof(f280,plain,(
% 1.61/0.56    ( ! [X4] : (~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | ~m1_subset_1(X4,u1_struct_0(sK6)) | sK7 != X4) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f279,f69])).
% 1.61/0.56  fof(f279,plain,(
% 1.61/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK6)) | ~v5_orders_2(sK6) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | sK7 != X4) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f278,f71])).
% 1.61/0.56  fof(f71,plain,(
% 1.61/0.56    v2_lattice3(sK6)),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f278,plain,(
% 1.61/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK6)) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | sK7 != X4) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f277,f72])).
% 1.61/0.56  fof(f277,plain,(
% 1.61/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | sK7 != X4) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f276,f73])).
% 1.61/0.56  fof(f276,plain,(
% 1.61/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | sK7 != X4) ) | (~spl11_3 | spl11_4)),
% 1.61/0.56    inference(subsumption_resolution,[],[f267,f185])).
% 1.61/0.56  fof(f185,plain,(
% 1.61/0.56    m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~spl11_3),
% 1.61/0.56    inference(avatar_component_clause,[],[f184])).
% 1.61/0.56  fof(f267,plain,(
% 1.61/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK6)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X4) | sK7 != X4) ) | spl11_4),
% 1.61/0.56    inference(resolution,[],[f250,f216])).
% 1.61/0.56  fof(f216,plain,(
% 1.61/0.56    ( ! [X0] : (~sP5(X0,sK6,k10_lattice3(sK6,sK7,sK8),sK7) | ~sP4(sK7,k10_lattice3(sK6,sK7,sK8),sK6,X0) | sK7 != X0) ) | spl11_4),
% 1.61/0.56    inference(superposition,[],[f190,f91])).
% 1.61/0.56  fof(f91,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (k11_lattice3(X1,X3,X2) = X0 | ~sP4(X3,X2,X1,X0) | ~sP5(X0,X1,X2,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f60])).
% 1.61/0.56  fof(f60,plain,(
% 1.61/0.56    ! [X0,X1,X2,X3] : (((k11_lattice3(X1,X3,X2) = X0 | ~sP4(X3,X2,X1,X0)) & (sP4(X3,X2,X1,X0) | k11_lattice3(X1,X3,X2) != X0)) | ~sP5(X0,X1,X2,X3))),
% 1.61/0.56    inference(rectify,[],[f59])).
% 1.61/0.56  fof(f59,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : (((k11_lattice3(X0,X1,X2) = X3 | ~sP4(X1,X2,X0,X3)) & (sP4(X1,X2,X0,X3) | k11_lattice3(X0,X1,X2) != X3)) | ~sP5(X3,X0,X2,X1))),
% 1.61/0.56    inference(nnf_transformation,[],[f44])).
% 1.61/0.56  fof(f44,plain,(
% 1.61/0.56    ! [X3,X0,X2,X1] : ((k11_lattice3(X0,X1,X2) = X3 <=> sP4(X1,X2,X0,X3)) | ~sP5(X3,X0,X2,X1))),
% 1.61/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.61/0.56  fof(f190,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | spl11_4),
% 1.61/0.56    inference(avatar_component_clause,[],[f188])).
% 1.61/0.56  fof(f250,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP5(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f101,f77])).
% 1.61/0.56  fof(f77,plain,(
% 1.61/0.56    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f19])).
% 1.61/0.56  fof(f19,plain,(
% 1.61/0.56    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f18])).
% 1.61/0.56  fof(f18,plain,(
% 1.61/0.56    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(ennf_transformation,[],[f3])).
% 1.61/0.56  fof(f3,axiom,(
% 1.61/0.56    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 1.61/0.56  fof(f101,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (sP5(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f45])).
% 1.61/0.56  fof(f45,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP5(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.56    inference(definition_folding,[],[f23,f44,f43,f42])).
% 1.61/0.56  fof(f23,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.56    inference(flattening,[],[f22])).
% 1.61/0.56  fof(f22,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f7])).
% 1.61/0.56  fof(f7,axiom,(
% 1.61/0.56    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 1.61/0.56  fof(f577,plain,(
% 1.61/0.56    spl11_5),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f576])).
% 1.61/0.56  fof(f576,plain,(
% 1.61/0.56    $false | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f575,f68])).
% 1.61/0.56  fof(f68,plain,(
% 1.61/0.56    v3_orders_2(sK6)),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  fof(f575,plain,(
% 1.61/0.56    ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f574,f71])).
% 1.61/0.56  fof(f574,plain,(
% 1.61/0.56    ~v2_lattice3(sK6) | ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f573,f69])).
% 1.61/0.56  fof(f573,plain,(
% 1.61/0.56    ~v5_orders_2(sK6) | ~v2_lattice3(sK6) | ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f572,f70])).
% 1.61/0.56  fof(f572,plain,(
% 1.61/0.56    ~v1_lattice3(sK6) | ~v5_orders_2(sK6) | ~v2_lattice3(sK6) | ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f571,f72])).
% 1.61/0.56  fof(f571,plain,(
% 1.61/0.56    ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6) | ~v2_lattice3(sK6) | ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(subsumption_resolution,[],[f569,f73])).
% 1.61/0.56  fof(f569,plain,(
% 1.61/0.56    ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6) | ~v2_lattice3(sK6) | ~v3_orders_2(sK6) | spl11_5),
% 1.61/0.56    inference(resolution,[],[f567,f318])).
% 1.61/0.56  fof(f318,plain,(
% 1.61/0.56    ~r1_orders_2(sK6,sK7,sK7) | spl11_5),
% 1.61/0.56    inference(avatar_component_clause,[],[f316])).
% 1.61/0.56  fof(f567,plain,(
% 1.61/0.56    ( ! [X0,X1] : (r1_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v2_lattice3(X1) | ~v3_orders_2(X1)) )),
% 1.61/0.56    inference(condensation,[],[f566])).
% 1.61/0.56  fof(f566,plain,(
% 1.61/0.56    ( ! [X17,X18,X16] : (r1_orders_2(X16,X18,X18) | ~l1_orders_2(X16) | ~v1_lattice3(X16) | ~v5_orders_2(X16) | ~m1_subset_1(X18,u1_struct_0(X16)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~v2_lattice3(X16) | ~v3_orders_2(X16)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f559,f108])).
% 1.61/0.56  fof(f108,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f37])).
% 1.61/0.56  fof(f37,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f36])).
% 1.61/0.56  fof(f36,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f5])).
% 1.61/0.56  fof(f5,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 1.61/0.56  fof(f559,plain,(
% 1.61/0.56    ( ! [X17,X18,X16] : (r1_orders_2(X16,X18,X18) | ~l1_orders_2(X16) | ~v1_lattice3(X16) | ~v5_orders_2(X16) | ~m1_subset_1(X18,u1_struct_0(X16)) | ~m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~v2_lattice3(X16) | ~v3_orders_2(X16)) )),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f556])).
% 1.61/0.56  fof(f556,plain,(
% 1.61/0.56    ( ! [X17,X18,X16] : (r1_orders_2(X16,X18,X18) | ~l1_orders_2(X16) | ~v1_lattice3(X16) | ~v5_orders_2(X16) | ~m1_subset_1(X18,u1_struct_0(X16)) | ~m1_subset_1(k11_lattice3(X16,X17,X18),u1_struct_0(X16)) | ~m1_subset_1(X18,u1_struct_0(X16)) | ~m1_subset_1(X17,u1_struct_0(X16)) | ~l1_orders_2(X16) | ~v2_lattice3(X16) | ~v1_lattice3(X16) | ~v5_orders_2(X16) | ~v3_orders_2(X16)) )),
% 1.61/0.56    inference(superposition,[],[f252,f534])).
% 1.61/0.56  fof(f534,plain,(
% 1.61/0.56    ( ! [X4,X5,X3] : (k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3)) )),
% 1.61/0.56    inference(subsumption_resolution,[],[f531,f108])).
% 1.61/0.56  fof(f531,plain,(
% 1.61/0.56    ( ! [X4,X5,X3] : (k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(k11_lattice3(X3,X4,X5),u1_struct_0(X3))) )),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f528])).
% 1.61/0.56  fof(f528,plain,(
% 1.61/0.56    ( ! [X4,X5,X3] : (k10_lattice3(X3,k11_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(k11_lattice3(X3,X4,X5),u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 1.61/0.56    inference(superposition,[],[f303,f105])).
% 1.61/0.56  fof(f105,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f31])).
% 1.61/0.56  fof(f31,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f30])).
% 1.61/0.56  fof(f30,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f9])).
% 1.61/0.56  fof(f9,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 1.61/0.56  fof(f303,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k13_lattice3(X0,k11_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.61/0.56    inference(duplicate_literal_removal,[],[f298])).
% 1.61/0.56  fof(f298,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k13_lattice3(X0,k11_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.61/0.56    inference(superposition,[],[f102,f106])).
% 1.61/0.56  fof(f106,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f33])).
% 1.61/0.56  fof(f33,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f32])).
% 1.61/0.56  fof(f32,plain,(
% 1.61/0.56    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f8])).
% 1.61/0.56  fof(f8,axiom,(
% 1.61/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 1.61/0.56  fof(f102,plain,(
% 1.61/0.56    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f25])).
% 1.61/0.56  fof(f25,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.61/0.56    inference(flattening,[],[f24])).
% 1.61/0.56  fof(f24,plain,(
% 1.61/0.56    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.61/0.56    inference(ennf_transformation,[],[f11])).
% 1.61/0.56  fof(f11,axiom,(
% 1.61/0.56    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 1.61/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).
% 1.61/0.56  fof(f252,plain,(
% 1.61/0.56    ( ! [X4,X5,X3] : (r1_orders_2(X4,X5,k10_lattice3(X4,X3,X5)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 1.61/0.56    inference(resolution,[],[f242,f81])).
% 1.61/0.56  fof(f81,plain,(
% 1.61/0.56    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_orders_2(X2,X1,X3)) )),
% 1.61/0.56    inference(cnf_transformation,[],[f54])).
% 1.61/0.56  fof(f204,plain,(
% 1.61/0.56    spl11_3),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f203])).
% 1.61/0.56  fof(f203,plain,(
% 1.61/0.56    $false | spl11_3),
% 1.61/0.56    inference(subsumption_resolution,[],[f202,f72])).
% 1.61/0.56  fof(f202,plain,(
% 1.61/0.56    ~l1_orders_2(sK6) | spl11_3),
% 1.61/0.56    inference(subsumption_resolution,[],[f201,f73])).
% 1.61/0.56  fof(f201,plain,(
% 1.61/0.56    ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | spl11_3),
% 1.61/0.56    inference(subsumption_resolution,[],[f199,f74])).
% 1.61/0.56  fof(f199,plain,(
% 1.61/0.56    ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | spl11_3),
% 1.61/0.56    inference(resolution,[],[f186,f107])).
% 1.61/0.56  fof(f186,plain,(
% 1.61/0.56    ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | spl11_3),
% 1.61/0.56    inference(avatar_component_clause,[],[f184])).
% 1.61/0.56  fof(f191,plain,(
% 1.61/0.56    ~spl11_3 | ~spl11_4),
% 1.61/0.56    inference(avatar_split_clause,[],[f182,f188,f184])).
% 1.61/0.56  fof(f182,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6))),
% 1.61/0.56    inference(subsumption_resolution,[],[f181,f69])).
% 1.61/0.56  fof(f181,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f180,f71])).
% 1.61/0.56  fof(f180,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f179,f72])).
% 1.61/0.56  fof(f179,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f165,f73])).
% 1.61/0.56  fof(f165,plain,(
% 1.61/0.56    sK7 != k11_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(k10_lattice3(sK6,sK7,sK8),u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v2_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(superposition,[],[f162,f106])).
% 1.61/0.56  fof(f162,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8))),
% 1.61/0.56    inference(subsumption_resolution,[],[f161,f69])).
% 1.61/0.56  fof(f161,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f160,f70])).
% 1.61/0.56  fof(f160,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f159,f72])).
% 1.61/0.56  fof(f159,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f158,f73])).
% 1.61/0.56  fof(f158,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(subsumption_resolution,[],[f157,f74])).
% 1.61/0.56  fof(f157,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k10_lattice3(sK6,sK7,sK8)) | ~m1_subset_1(sK8,u1_struct_0(sK6)) | ~m1_subset_1(sK7,u1_struct_0(sK6)) | ~l1_orders_2(sK6) | ~v1_lattice3(sK6) | ~v5_orders_2(sK6)),
% 1.61/0.56    inference(superposition,[],[f75,f105])).
% 1.61/0.56  fof(f75,plain,(
% 1.61/0.56    sK7 != k12_lattice3(sK6,sK7,k13_lattice3(sK6,sK7,sK8))),
% 1.61/0.56    inference(cnf_transformation,[],[f49])).
% 1.61/0.56  % SZS output end Proof for theBenchmark
% 1.61/0.56  % (24166)------------------------------
% 1.61/0.56  % (24166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.56  % (24166)Termination reason: Refutation
% 1.61/0.56  
% 1.61/0.56  % (24166)Memory used [KB]: 6396
% 1.61/0.56  % (24166)Time elapsed: 0.147 s
% 1.61/0.56  % (24166)------------------------------
% 1.61/0.56  % (24166)------------------------------
% 1.61/0.57  % (24161)Success in time 0.208 s
%------------------------------------------------------------------------------
