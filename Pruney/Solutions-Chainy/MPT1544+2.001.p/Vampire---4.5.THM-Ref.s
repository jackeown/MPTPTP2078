%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 609 expanded)
%              Number of leaves         :   14 ( 136 expanded)
%              Depth                    :   37
%              Number of atoms          : 1040 (5388 expanded)
%              Number of equality atoms :   72 ( 427 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f76,f119,f133,f178,f183,f187,f205])).

fof(f205,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_9 ),
    inference(subsumption_resolution,[],[f203,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f202,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k13_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f202,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f201,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f201,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f200,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f199,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f199,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f198,f25])).

fof(f25,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f198,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f197,f24])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f197,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f196,f45])).

fof(f45,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f196,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(superposition,[],[f36,f103])).

fof(f103,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f102,f24])).

fof(f102,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f101,f22])).

fof(f101,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f100,f23])).

fof(f100,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f99,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f97,f25])).

fof(f97,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_1 ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f42,plain,
    ( sK3 = k13_lattice3(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl6_1
  <=> sK3 = k13_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f187,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f185,f26])).

fof(f185,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f184,f25])).

fof(f184,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f92,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f183,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f182,f74,f94,f90])).

fof(f94,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | sK3 = k10_lattice3(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f74,plain,
    ( spl6_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X4)
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,X1) )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f181,f21])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,X1) )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f180,f26])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,X1) )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f179,f25])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,X1) )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f136,f24])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,X1,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,X1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK5(X0,X1,X2,X3))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f178,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f176,f82])).

fof(f82,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f78,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f77,f25])).

fof(f77,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl6_1 ),
    inference(superposition,[],[f41,f35])).

fof(f41,plain,
    ( sK3 != k13_lattice3(sK0,sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f176,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f175,f91])).

fof(f175,plain,
    ( v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f174,f46])).

fof(f46,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f174,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f173,f51])).

fof(f51,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_3
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f173,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f172,f21])).

fof(f172,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f171,f22])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f170,f23])).

fof(f170,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f169,f26])).

fof(f169,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f168,f25])).

fof(f168,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f167,f24])).

fof(f167,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f166,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f166,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f165,f91])).

fof(f165,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f164,f46])).

fof(f164,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f163,f21])).

fof(f163,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f162,f22])).

fof(f162,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f161,f26])).

fof(f161,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f160,f25])).

fof(f160,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f159,f24])).

fof(f159,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f158,f82])).

fof(f158,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f157,f23])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f156,f51])).

fof(f156,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | v2_struct_0(sK0)
    | sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f147,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK5(X0,X1,X2,X3))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) )
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f146,f91])).

fof(f146,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f145,f21])).

fof(f145,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f144,f26])).

fof(f144,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f143,f25])).

fof(f143,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f142,f24])).

% (30721)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f142,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f141,f22])).

fof(f141,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f140,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( sK3 = k10_lattice3(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | v2_struct_0(sK0)
        | sK3 = k10_lattice3(sK0,X0,sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f95,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK5(X0,X1,X2,X3))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | v2_struct_0(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3))
        | sK3 = k10_lattice3(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3))
        | ~ m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f133,plain,
    ( ~ spl6_1
    | spl6_3
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl6_1
    | spl6_3
    | spl6_9 ),
    inference(subsumption_resolution,[],[f50,f131])).

fof(f131,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_1
    | spl6_9 ),
    inference(subsumption_resolution,[],[f130,f91])).

fof(f130,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f129,f21])).

fof(f129,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f128,f22])).

fof(f128,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f127,f23])).

fof(f127,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f126,f26])).

fof(f126,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f125,f25])).

fof(f125,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f105,f24])).

fof(f105,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(superposition,[],[f37,f103])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f119,plain,
    ( ~ spl6_1
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl6_1
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(subsumption_resolution,[],[f117,f61])).

fof(f61,plain,
    ( r1_orders_2(sK0,sK2,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl6_5
  <=> r1_orders_2(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f117,plain,
    ( ~ r1_orders_2(sK0,sK2,sK4)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | spl6_9 ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f66,plain,
    ( r1_orders_2(sK0,sK1,sK4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_6
  <=> r1_orders_2(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f116,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK4)
    | ~ spl6_1
    | spl6_4
    | ~ spl6_7
    | spl6_9 ),
    inference(subsumption_resolution,[],[f114,f71])).

fof(f71,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f114,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK4)
    | ~ spl6_1
    | spl6_4
    | spl6_9 ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_4
  <=> r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f113,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl6_1
    | spl6_9 ),
    inference(subsumption_resolution,[],[f112,f91])).

fof(f112,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f111,f21])).

fof(f111,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f110,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f109,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f108,f26])).

fof(f108,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f107,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f38,f103])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,X3,X4)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,
    ( spl6_1
    | spl6_8 ),
    inference(avatar_split_clause,[],[f14,f74,f40])).

fof(f14,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK1,X4)
      | ~ r1_orders_2(sK0,sK2,X4)
      | r1_orders_2(sK0,sK3,X4)
      | sK3 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,
    ( ~ spl6_1
    | spl6_7
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f15,f49,f44,f69,f40])).

fof(f15,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,
    ( ~ spl6_1
    | spl6_6
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f16,f49,f44,f64,f40])).

fof(f16,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,
    ( ~ spl6_1
    | spl6_5
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f17,f49,f44,f59,f40])).

fof(f17,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f18,f49,f44,f54,f40])).

fof(f18,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f19,f49,f40])).

fof(f19,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f20,f44,f40])).

fof(f20,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (30714)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (30706)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (30708)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (30707)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (30711)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (30725)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (30707)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (30724)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f76,f119,f133,f178,f183,f187,f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~spl6_1 | spl6_2 | spl6_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_2 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl6_9 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f202,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k13_lattice3(X0,X1,X2) = X3 <~> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k13_lattice3(X0,X1,X2) = X3 <~> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f201,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f199,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    l1_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f198,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    v1_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f197,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    v5_orders_2(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_1 | spl6_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f196,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK2,sK3) | spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl6_2 <=> r1_orders_2(sK0,sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK2,sK3) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(superposition,[],[f36,f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f24])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f22])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f23])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f26])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f25])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~spl6_1),
% 0.22/0.51    inference(superposition,[],[f42,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    sK3 = k13_lattice3(sK0,sK1,sK2) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl6_1 <=> sK3 = k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ~spl6_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    $false | ~spl6_9),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f26])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~l1_orders_2(sK0) | ~spl6_9),
% 0.22/0.51    inference(subsumption_resolution,[],[f184,f25])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl6_9),
% 0.22/0.51    inference(resolution,[],[f92,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    spl6_9 | spl6_10 | ~spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f182,f74,f94,f90])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl6_10 <=> ! [X1,X0] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | sK3 = k10_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X1,sK3) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl6_8 <=> ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,X4) | ~r1_orders_2(sK0,sK2,X4) | ~r1_orders_2(sK0,sK1,X4))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,X1,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,X1)) ) | ~spl6_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f181,f21])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,X1,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,X1)) ) | ~spl6_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f26])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,X1,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,X1)) ) | ~spl6_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f179,f25])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,X1,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,X1)) ) | ~spl6_8),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f24])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,X1,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,X1)) ) | ~spl6_8),
% 0.22/0.51    inference(resolution,[],[f75,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X3,sK5(X0,X1,X2,X3)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X4] : (r1_orders_2(sK0,sK3,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X4) | ~r1_orders_2(sK0,sK1,X4)) ) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f74])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f24])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | ~v5_orders_2(sK0) | spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f22])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f79,f23])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f26])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f77,f25])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    sK3 != k10_lattice3(sK0,sK1,sK2) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl6_1),
% 0.22/0.51    inference(superposition,[],[f41,f35])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    sK3 != k13_lattice3(sK0,sK1,sK2) | spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f175,f91])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK2,sK3) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl6_3 <=> r1_orders_2(sK0,sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f21])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f22])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f23])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f26])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f25])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f24])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(resolution,[],[f166,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f91])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f46])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f21])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f162,f22])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f161,f26])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f25])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f24])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f82])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f23])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f51])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | (~spl6_2 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f155])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK3 = k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,sK1,sK2) | (~spl6_2 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(resolution,[],[f147,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,sK5(X0,X1,X2,X3)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK3 = k10_lattice3(sK0,X0,sK2) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0))) ) | (~spl6_2 | spl6_9 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f91])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f21])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f144,f26])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f143,f25])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f24])).
% 0.22/0.51  % (30721)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f22])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f46])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl6_10),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X0] : (sK3 = k10_lattice3(sK0,X0,sK2) | ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,sK2,sK3)) | ~m1_subset_1(sK5(sK0,X0,sK2,sK3),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r1_orders_2(sK0,sK2,sK3) | v2_struct_0(sK0) | sK3 = k10_lattice3(sK0,X0,sK2)) ) | ~spl6_10),
% 0.22/0.51    inference(resolution,[],[f95,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK5(X0,X1,X2,X3)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,sK2,sK5(sK0,X0,X1,sK3)) | sK3 = k10_lattice3(sK0,X0,X1) | ~r1_orders_2(sK0,X1,sK3) | ~r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK5(sK0,X0,X1,sK3)) | ~m1_subset_1(sK5(sK0,X0,X1,sK3),u1_struct_0(sK0))) ) | ~spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f94])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ~spl6_1 | spl6_3 | spl6_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_3 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f50,f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | (~spl6_1 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f130,f91])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f21])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f22])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f23])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f126,f26])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f25])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f24])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl6_1),
% 0.22/0.51    inference(superposition,[],[f37,f103])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f49])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~spl6_1 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK2,sK4) | ~spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl6_5 <=> r1_orders_2(sK0,sK2,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK2,sK4) | (~spl6_1 | spl6_4 | ~spl6_6 | ~spl6_7 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK4) | ~spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl6_6 <=> r1_orders_2(sK0,sK1,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK4) | ~r1_orders_2(sK0,sK2,sK4) | (~spl6_1 | spl6_4 | ~spl6_7 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl6_7 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK4) | ~r1_orders_2(sK0,sK2,sK4) | (~spl6_1 | spl6_4 | spl6_9)),
% 0.22/0.51    inference(resolution,[],[f113,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK3,sK4) | spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl6_4 <=> r1_orders_2(sK0,sK3,sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0)) ) | (~spl6_1 | spl6_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f91])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f111,f21])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f22])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f23])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f26])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f25])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f24])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0] : (r1_orders_2(sK0,sK3,X0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~r1_orders_2(sK0,sK2,X0) | v2_struct_0(sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(superposition,[],[f38,f103])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X4) | ~r1_orders_2(X0,X2,X4) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X4) | ~r1_orders_2(X0,X2,X4) | r1_orders_2(X0,X3,X4) | k10_lattice3(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl6_1 | spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f14,f74,f40])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X4) | ~r1_orders_2(sK0,sK2,X4) | r1_orders_2(sK0,sK3,X4) | sK3 = k13_lattice3(sK0,sK1,sK2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ~spl6_1 | spl6_7 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f15,f49,f44,f69,f40])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | m1_subset_1(sK4,u1_struct_0(sK0)) | sK3 != k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~spl6_1 | spl6_6 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f49,f44,f64,f40])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK1,sK4) | sK3 != k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ~spl6_1 | spl6_5 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f49,f44,f59,f40])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK2,sK4) | sK3 != k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~spl6_1 | ~spl6_4 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f49,f44,f54,f40])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ~r1_orders_2(sK0,sK1,sK3) | ~r1_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK0,sK3,sK4) | sK3 != k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl6_1 | spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f49,f40])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK1,sK3) | sK3 = k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl6_1 | spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f44,f40])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    r1_orders_2(sK0,sK2,sK3) | sK3 = k13_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (30707)------------------------------
% 0.22/0.51  % (30707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30707)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (30707)Memory used [KB]: 10746
% 0.22/0.51  % (30707)Time elapsed: 0.077 s
% 0.22/0.51  % (30707)------------------------------
% 0.22/0.51  % (30707)------------------------------
% 0.22/0.52  % (30705)Success in time 0.156 s
%------------------------------------------------------------------------------
