%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:33 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 385 expanded)
%              Number of leaves         :   14 ( 117 expanded)
%              Depth                    :   24
%              Number of atoms          :  968 (2339 expanded)
%              Number of equality atoms :   72 ( 130 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1747,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f72,f77,f82,f166,f476,f1346,f1665,f1746])).

fof(f1746,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_24
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f1745])).

fof(f1745,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_24
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1512,f1664])).

fof(f1664,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f1662])).

fof(f1662,plain,
    ( spl8_28
  <=> m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f1512,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1511,f71])).

fof(f71,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1511,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1510,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl8_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1510,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_6
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1423,f81])).

fof(f81,plain,
    ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_6
  <=> k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1423,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(superposition,[],[f699,f1345])).

fof(f1345,plain,
    ( k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f1343])).

fof(f1343,plain,
    ( spl8_24
  <=> k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f699,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f698,f84])).

fof(f84,plain,
    ( ! [X6,X5] :
        ( r1_orders_2(sK0,X6,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f64,f54])).

fof(f54,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f64,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,sK5(sK0,X5,X6))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f49,plain,
    ( v1_lattice3(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_2
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f698,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f697,f83])).

fof(f83,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,X3,sK5(sK0,X3,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f63,f54])).

fof(f63,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK5(sK0,X3,X4))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f697,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X1,X0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f696,f89])).

fof(f89,plain,
    ( ! [X4,X5,X3] :
        ( r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f88,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f60,f49])).

fof(f60,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f57,f20])).

fof(f20,plain,(
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

fof(f57,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ r1_orders_2(sK0,X4,X5)
        | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5))
        | k10_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f44,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl8_1
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f696,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X1,X0,sK5(sK0,X1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X1,X0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f691])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X1,X0,sK5(sK0,X1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X1,X0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f624,f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f86,f54])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f59,f49])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2))
        | k10_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f624,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X3,sK7(sK0,X3,X2,sK5(sK0,X3,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X3,X2,sK5(sK0,X3,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f620])).

fof(f620,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X2,sK7(sK0,X3,X2,sK5(sK0,X3,X2)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X3,X2,sK5(sK0,X3,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X2) = sK5(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f496,f84])).

fof(f496,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X2,sK5(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X2,sK5(sK0,X0,X1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k10_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X2,sK5(sK0,X0,X1)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X2,sK5(sK0,X0,X1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k10_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f480,f83])).

fof(f480,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f479,f49])).

fof(f479,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ v1_lattice3(sK0) )
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f478,f54])).

fof(f478,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f165,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f165,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_8
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1665,plain,
    ( spl8_28
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f1528,f1343,f74,f69,f52,f47,f1662])).

fof(f1528,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1527,f49])).

fof(f1527,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1526,f54])).

fof(f1526,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1525,f71])).

fof(f1525,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl8_5
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f1430,f76])).

fof(f1430,plain,
    ( m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl8_24 ),
    inference(superposition,[],[f26,f1345])).

fof(f1346,plain,
    ( spl8_24
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1327,f164,f74,f69,f52,f47,f42,f1343])).

fof(f1327,plain,
    ( k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(resolution,[],[f1201,f76])).

fof(f1201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK2,X0) = sK5(sK0,X0,sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f851,f71])).

fof(f851,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f850,f49])).

fof(f850,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f849,f54])).

fof(f849,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f847])).

fof(f847,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f686,f26])).

fof(f686,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f685,f83])).

fof(f685,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)
        | ~ m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f684,f84])).

fof(f684,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)
        | ~ m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X1))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f680,f87])).

fof(f680,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,sK7(sK0,X1,X2,sK5(sK0,X2,X1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)
        | ~ m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X1))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f677])).

fof(f677,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,sK7(sK0,X1,X2,sK5(sK0,X2,X1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X1))
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f612,f89])).

fof(f612,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1,sK5(sK0,X1,X0)))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X1,sK5(sK0,X1,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,X0,X1,sK5(sK0,X1,X0)))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X1,sK5(sK0,X1,X0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f495,f83])).

fof(f495,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK0,X5,sK5(sK0,X3,X4))
        | ~ r1_orders_2(sK0,X4,sK7(sK0,X4,X5,sK5(sK0,X3,X4)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X4,X5,sK5(sK0,X3,X4)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | sK5(sK0,X3,X4) = k10_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK7(sK0,X4,X5,sK5(sK0,X3,X4)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X4,X5,sK5(sK0,X3,X4)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | sK5(sK0,X3,X4) = k10_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK5(sK0,X3,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f480,f84])).

fof(f476,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f474,f54])).

fof(f474,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f473,f49])).

fof(f473,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f162,f20])).

fof(f162,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f166,plain,
    ( spl8_7
    | spl8_8
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f135,f52,f47,f42,f164,f160])).

fof(f135,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f134,f54])).

fof(f134,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1,X2))
        | ~ r1_orders_2(sK0,X3,sK5(sK0,X1,X2))
        | v2_struct_0(sK0)
        | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f108,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f13])).

fof(f108,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK5(sK0,X2,X3))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X2,X3))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f94,f26])).

fof(f94,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,sK5(sK0,X5,X6))
        | ~ r1_orders_2(sK0,X4,sK5(sK0,X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | sK5(sK0,X5,X6) = k10_lattice3(sK0,X7,X4)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK7(sK0,X7,X4,sK5(sK0,X5,X6)))
        | ~ r1_orders_2(sK0,X6,sK7(sK0,X7,X4,sK5(sK0,X5,X6)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f62,f54])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,sK5(X0,X1,X2),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f90,plain,
    ( ! [X6,X8,X7] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f61,f49])).

fof(f61,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f58,f20])).

fof(f58,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8))
        | k10_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f15,f79])).

fof(f15,plain,(
    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
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
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
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
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
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
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

fof(f77,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f16,f74])).

fof(f16,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f14,f69])).

fof(f14,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (8328)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (8320)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (8314)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (8331)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (8316)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (8314)Refutation not found, incomplete strategy% (8314)------------------------------
% 0.21/0.48  % (8314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8314)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8314)Memory used [KB]: 10618
% 0.21/0.48  % (8314)Time elapsed: 0.070 s
% 0.21/0.48  % (8314)------------------------------
% 0.21/0.48  % (8314)------------------------------
% 0.21/0.48  % (8318)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8322)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8325)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8317)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (8321)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (8315)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (8327)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (8313)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (8333)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (8333)Refutation not found, incomplete strategy% (8333)------------------------------
% 0.21/0.50  % (8333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8333)Memory used [KB]: 10618
% 0.21/0.50  % (8333)Time elapsed: 0.091 s
% 0.21/0.50  % (8333)------------------------------
% 0.21/0.50  % (8333)------------------------------
% 0.21/0.50  % (8324)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (8319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (8332)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (8326)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (8329)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (8330)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (8323)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.65/0.58  % (8316)Refutation found. Thanks to Tanya!
% 1.65/0.58  % SZS status Theorem for theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f1747,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f45,f50,f55,f72,f77,f82,f166,f476,f1346,f1665,f1746])).
% 1.65/0.58  fof(f1746,plain,(
% 1.65/0.58    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_24 | ~spl8_28),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1745])).
% 1.65/0.58  fof(f1745,plain,(
% 1.65/0.58    $false | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_24 | ~spl8_28)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1512,f1664])).
% 1.65/0.58  fof(f1664,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl8_28),
% 1.65/0.58    inference(avatar_component_clause,[],[f1662])).
% 1.65/0.58  fof(f1662,plain,(
% 1.65/0.58    spl8_28 <=> m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.65/0.58  fof(f1512,plain,(
% 1.65/0.58    ~m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1511,f71])).
% 1.65/0.58  fof(f71,plain,(
% 1.65/0.58    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl8_4),
% 1.65/0.58    inference(avatar_component_clause,[],[f69])).
% 1.65/0.58  fof(f69,plain,(
% 1.65/0.58    spl8_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.65/0.58  fof(f1511,plain,(
% 1.65/0.58    ~m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1510,f76])).
% 1.65/0.58  fof(f76,plain,(
% 1.65/0.58    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_5),
% 1.65/0.58    inference(avatar_component_clause,[],[f74])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    spl8_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.65/0.58  fof(f1510,plain,(
% 1.65/0.58    ~m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_6 | ~spl8_8 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1423,f81])).
% 1.65/0.58  fof(f81,plain,(
% 1.65/0.58    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) | spl8_6),
% 1.65/0.58    inference(avatar_component_clause,[],[f79])).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    spl8_6 <=> k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.65/0.58  fof(f1423,plain,(
% 1.65/0.58    ~m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | k10_lattice3(sK0,sK1,sK2) = k10_lattice3(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8 | ~spl8_24)),
% 1.65/0.58    inference(superposition,[],[f699,f1345])).
% 1.65/0.58  fof(f1345,plain,(
% 1.65/0.58    k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2) | ~spl8_24),
% 1.65/0.58    inference(avatar_component_clause,[],[f1343])).
% 1.65/0.58  fof(f1343,plain,(
% 1.65/0.58    spl8_24 <=> k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.65/0.58  fof(f699,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f698,f84])).
% 1.65/0.58  fof(f84,plain,(
% 1.65/0.58    ( ! [X6,X5] : (r1_orders_2(sK0,X6,sK5(sK0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f64,f54])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    l1_orders_2(sK0) | ~spl8_3),
% 1.65/0.58    inference(avatar_component_clause,[],[f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    spl8_3 <=> l1_orders_2(sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,X6,sK5(sK0,X5,X6)) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.65/0.58    inference(resolution,[],[f49,f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,plain,(
% 1.65/0.58    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.65/0.58    inference(flattening,[],[f10])).
% 1.65/0.58  fof(f10,plain,(
% 1.65/0.58    ! [X0] : ((v1_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_lattice3)).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    v1_lattice3(sK0) | ~spl8_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f47])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    spl8_2 <=> v1_lattice3(sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.65/0.58  fof(f698,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f697,f83])).
% 1.65/0.58  fof(f83,plain,(
% 1.65/0.58    ( ! [X4,X3] : (r1_orders_2(sK0,X3,sK5(sK0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f63,f54])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,sK5(sK0,X3,X4)) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.65/0.58    inference(resolution,[],[f49,f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f11])).
% 1.65/0.58  fof(f697,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X1,X0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f696,f89])).
% 1.65/0.58  fof(f89,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X4) = X5) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f88,f54])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | (~spl8_1 | ~spl8_2)),
% 1.65/0.58    inference(subsumption_resolution,[],[f60,f49])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | ~spl8_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f57,f20])).
% 1.65/0.58  fof(f20,plain,(
% 1.65/0.58    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,plain,(
% 1.65/0.58    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.65/0.58    inference(flattening,[],[f8])).
% 1.65/0.58  fof(f8,plain,(
% 1.65/0.58    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X5) | ~r1_orders_2(sK0,X4,X5) | r1_orders_2(sK0,X4,sK7(sK0,X3,X4,X5)) | k10_lattice3(sK0,X3,X4) = X5) ) | ~spl8_1),
% 1.65/0.58    inference(resolution,[],[f44,f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 1.65/0.58    inference(cnf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.65/0.58    inference(flattening,[],[f12])).
% 1.65/0.58  fof(f12,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    v5_orders_2(sK0) | ~spl8_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    spl8_1 <=> v5_orders_2(sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.65/0.58  fof(f696,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK7(sK0,X1,X0,sK5(sK0,X1,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X1,X0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f691])).
% 1.65/0.58  fof(f691,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK7(sK0,X1,X0,sK5(sK0,X1,X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X1,X0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X1,X0) = k10_lattice3(sK0,X1,X0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f624,f87])).
% 1.65/0.58  fof(f87,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = X2) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f86,f54])).
% 1.65/0.58  fof(f86,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | (~spl8_1 | ~spl8_2)),
% 1.65/0.58    inference(subsumption_resolution,[],[f59,f49])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | ~spl8_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f56,f20])).
% 1.65/0.58  fof(f56,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,X0,sK7(sK0,X0,X1,X2)) | k10_lattice3(sK0,X0,X1) = X2) ) | ~spl8_1),
% 1.65/0.58    inference(resolution,[],[f44,f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 1.65/0.58    inference(cnf_transformation,[],[f13])).
% 1.65/0.58  fof(f624,plain,(
% 1.65/0.58    ( ! [X2,X3] : (~r1_orders_2(sK0,X3,sK7(sK0,X3,X2,sK5(sK0,X3,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X3,X2,sK5(sK0,X3,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f620])).
% 1.65/0.58  fof(f620,plain,(
% 1.65/0.58    ( ! [X2,X3] : (~r1_orders_2(sK0,X2,sK7(sK0,X3,X2,sK5(sK0,X3,X2))) | ~r1_orders_2(sK0,X3,sK7(sK0,X3,X2,sK5(sK0,X3,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X2) = sK5(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f496,f84])).
% 1.65/0.58  fof(f496,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X2,sK5(sK0,X0,X1))) | ~r1_orders_2(sK0,X0,sK7(sK0,X0,X2,sK5(sK0,X0,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k10_lattice3(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f492])).
% 1.65/0.58  fof(f492,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X2,sK5(sK0,X0,X1))) | ~r1_orders_2(sK0,X0,sK7(sK0,X0,X2,sK5(sK0,X0,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k10_lattice3(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f480,f83])).
% 1.65/0.58  fof(f480,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f479,f49])).
% 1.65/0.58  fof(f479,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~v1_lattice3(sK0)) ) | (~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f478,f54])).
% 1.65/0.58  fof(f478,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | ~spl8_8),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f477])).
% 1.65/0.58  fof(f477,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | ~spl8_8),
% 1.65/0.58    inference(resolution,[],[f165,f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f11])).
% 1.65/0.58  fof(f165,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2))) ) | ~spl8_8),
% 1.65/0.58    inference(avatar_component_clause,[],[f164])).
% 1.65/0.58  fof(f164,plain,(
% 1.65/0.58    spl8_8 <=> ! [X1,X3,X0,X2] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.65/0.58  fof(f1665,plain,(
% 1.65/0.58    spl8_28 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_24),
% 1.65/0.58    inference(avatar_split_clause,[],[f1528,f1343,f74,f69,f52,f47,f1662])).
% 1.65/0.58  fof(f1528,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1527,f49])).
% 1.65/0.58  fof(f1527,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1526,f54])).
% 1.65/0.58  fof(f1526,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1525,f71])).
% 1.65/0.58  fof(f1525,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | (~spl8_5 | ~spl8_24)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1430,f76])).
% 1.65/0.58  fof(f1430,plain,(
% 1.65/0.58    m1_subset_1(k10_lattice3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~spl8_24),
% 1.65/0.58    inference(superposition,[],[f26,f1345])).
% 1.65/0.58  fof(f1346,plain,(
% 1.65/0.58    spl8_24 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f1327,f164,f74,f69,f52,f47,f42,f1343])).
% 1.65/0.58  fof(f1327,plain,(
% 1.65/0.58    k10_lattice3(sK0,sK2,sK1) = sK5(sK0,sK1,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f1201,f76])).
% 1.65/0.58  fof(f1201,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,sK2,X0) = sK5(sK0,X0,sK2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f851,f71])).
% 1.65/0.58  fof(f851,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f850,f49])).
% 1.65/0.58  fof(f850,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f849,f54])).
% 1.65/0.58  fof(f849,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f847])).
% 1.65/0.58  fof(f847,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f686,f26])).
% 1.65/0.58  fof(f686,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f685,f83])).
% 1.65/0.58  fof(f685,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) | ~m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X1))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f684,f84])).
% 1.65/0.58  fof(f684,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) | ~m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X1)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X1))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(subsumption_resolution,[],[f680,f87])).
% 1.65/0.58  fof(f680,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~r1_orders_2(sK0,X1,sK7(sK0,X1,X2,sK5(sK0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) | ~m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X1)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X1))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f677])).
% 1.65/0.58  fof(f677,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~r1_orders_2(sK0,X1,sK7(sK0,X1,X2,sK5(sK0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X1)) | ~r1_orders_2(sK0,X2,sK5(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X2) = sK5(sK0,X2,X1)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f612,f89])).
% 1.65/0.58  fof(f612,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,sK7(sK0,X0,X1,sK5(sK0,X1,X0))) | ~r1_orders_2(sK0,X0,sK7(sK0,X0,X1,sK5(sK0,X1,X0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0)) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f606])).
% 1.65/0.58  fof(f606,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,sK7(sK0,X0,X1,sK5(sK0,X1,X0))) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X1,sK5(sK0,X1,X0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X0,X1) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f495,f83])).
% 1.65/0.58  fof(f495,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~r1_orders_2(sK0,X5,sK5(sK0,X3,X4)) | ~r1_orders_2(sK0,X4,sK7(sK0,X4,X5,sK5(sK0,X3,X4))) | ~r1_orders_2(sK0,X3,sK7(sK0,X4,X5,sK5(sK0,X3,X4))) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | sK5(sK0,X3,X4) = k10_lattice3(sK0,X4,X5) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f493])).
% 1.65/0.58  fof(f493,plain,(
% 1.65/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X4,sK7(sK0,X4,X5,sK5(sK0,X3,X4))) | ~r1_orders_2(sK0,X3,sK7(sK0,X4,X5,sK5(sK0,X3,X4))) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | sK5(sK0,X3,X4) = k10_lattice3(sK0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,sK5(sK0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.65/0.58    inference(resolution,[],[f480,f84])).
% 1.65/0.58  fof(f476,plain,(
% 1.65/0.58    ~spl8_2 | ~spl8_3 | ~spl8_7),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f475])).
% 1.65/0.58  fof(f475,plain,(
% 1.65/0.58    $false | (~spl8_2 | ~spl8_3 | ~spl8_7)),
% 1.65/0.58    inference(subsumption_resolution,[],[f474,f54])).
% 1.65/0.58  fof(f474,plain,(
% 1.65/0.58    ~l1_orders_2(sK0) | (~spl8_2 | ~spl8_7)),
% 1.65/0.58    inference(subsumption_resolution,[],[f473,f49])).
% 1.65/0.58  fof(f473,plain,(
% 1.65/0.58    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl8_7),
% 1.65/0.58    inference(resolution,[],[f162,f20])).
% 1.65/0.58  fof(f162,plain,(
% 1.65/0.58    v2_struct_0(sK0) | ~spl8_7),
% 1.65/0.58    inference(avatar_component_clause,[],[f160])).
% 1.65/0.58  fof(f160,plain,(
% 1.65/0.58    spl8_7 <=> v2_struct_0(sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.65/0.58  fof(f166,plain,(
% 1.65/0.58    spl8_7 | spl8_8 | ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f135,f52,f47,f42,f164,f160])).
% 1.65/0.58  fof(f135,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f134,f54])).
% 1.65/0.58  fof(f134,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f133,f49])).
% 1.65/0.58  fof(f133,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f132,f44])).
% 1.65/0.58  fof(f132,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f131])).
% 1.65/0.58  fof(f131,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~r1_orders_2(sK0,X2,sK7(sK0,X0,X3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~r1_orders_2(sK0,X3,sK5(sK0,X1,X2)) | v2_struct_0(sK0) | sK5(sK0,X1,X2) = k10_lattice3(sK0,X0,X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(resolution,[],[f108,f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | v2_struct_0(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 1.65/0.58    inference(cnf_transformation,[],[f13])).
% 1.65/0.58  fof(f108,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f107,f49])).
% 1.65/0.58  fof(f107,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f106,f54])).
% 1.65/0.58  fof(f106,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f105])).
% 1.65/0.58  fof(f105,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK5(sK0,X2,X3)) | ~r1_orders_2(sK0,X0,sK5(sK0,X2,X3)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = sK5(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X1,X0,sK5(sK0,X2,X3)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~r1_orders_2(sK0,X3,sK7(sK0,X1,X0,sK5(sK0,X2,X3))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(resolution,[],[f94,f26])).
% 1.65/0.58  fof(f94,plain,(
% 1.65/0.58    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X7,sK5(sK0,X5,X6)) | ~r1_orders_2(sK0,X4,sK5(sK0,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | sK5(sK0,X5,X6) = k10_lattice3(sK0,X7,X4) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,sK7(sK0,X7,X4,sK5(sK0,X5,X6))) | ~r1_orders_2(sK0,X6,sK7(sK0,X7,X4,sK5(sK0,X5,X6))) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(resolution,[],[f91,f85])).
% 1.65/0.58  fof(f85,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f62,f54])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X2) | ~r1_orders_2(sK0,X1,X2) | r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.65/0.58    inference(resolution,[],[f49,f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X4) | ~r1_orders_2(X0,X2,X4) | r1_orders_2(X0,sK5(X0,X1,X2),X4) | ~l1_orders_2(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f11])).
% 1.65/0.58  fof(f91,plain,(
% 1.65/0.58    ( ! [X6,X8,X7] : (~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k10_lattice3(sK0,X6,X7) = X8) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.65/0.58    inference(subsumption_resolution,[],[f90,f54])).
% 1.65/0.58  fof(f90,plain,(
% 1.65/0.58    ( ! [X6,X8,X7] : (~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | (~spl8_1 | ~spl8_2)),
% 1.65/0.58    inference(subsumption_resolution,[],[f61,f49])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    ( ! [X6,X8,X7] : (~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | ~spl8_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f58,f20])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    ( ! [X6,X8,X7] : (v2_struct_0(sK0) | ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,X8) | ~r1_orders_2(sK0,X7,X8) | ~r1_orders_2(sK0,X8,sK7(sK0,X6,X7,X8)) | k10_lattice3(sK0,X6,X7) = X8) ) | ~spl8_1),
% 1.65/0.58    inference(resolution,[],[f44,f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X3,sK7(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3) )),
% 1.65/0.58    inference(cnf_transformation,[],[f13])).
% 1.65/0.58  fof(f82,plain,(
% 1.65/0.58    ~spl8_6),
% 1.65/0.58    inference(avatar_split_clause,[],[f15,f79])).
% 1.65/0.58  fof(f15,plain,(
% 1.65/0.58    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,plain,(
% 1.65/0.58    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 1.65/0.58    inference(flattening,[],[f6])).
% 1.65/0.58  fof(f6,plain,(
% 1.65/0.58    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,negated_conjecture,(
% 1.65/0.58    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 1.65/0.58    inference(negated_conjecture,[],[f4])).
% 1.65/0.58  fof(f4,conjecture,(
% 1.65/0.58    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    spl8_5),
% 1.65/0.58    inference(avatar_split_clause,[],[f16,f74])).
% 1.65/0.58  fof(f16,plain,(
% 1.65/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    spl8_4),
% 1.65/0.58    inference(avatar_split_clause,[],[f14,f69])).
% 1.65/0.58  fof(f14,plain,(
% 1.65/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    spl8_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f19,f52])).
% 1.65/0.58  fof(f19,plain,(
% 1.65/0.58    l1_orders_2(sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    spl8_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f18,f47])).
% 1.65/0.58  fof(f18,plain,(
% 1.65/0.58    v1_lattice3(sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    spl8_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f17,f42])).
% 1.65/0.58  fof(f17,plain,(
% 1.65/0.58    v5_orders_2(sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (8316)------------------------------
% 1.65/0.58  % (8316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (8316)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (8316)Memory used [KB]: 11641
% 1.65/0.58  % (8316)Time elapsed: 0.167 s
% 1.65/0.58  % (8316)------------------------------
% 1.65/0.58  % (8316)------------------------------
% 1.65/0.58  % (8312)Success in time 0.228 s
%------------------------------------------------------------------------------
