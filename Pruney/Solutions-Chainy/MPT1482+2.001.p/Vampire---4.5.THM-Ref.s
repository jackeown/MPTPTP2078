%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:33 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 385 expanded)
%              Number of leaves         :   14 ( 117 expanded)
%              Depth                    :   27
%              Number of atoms          : 1008 (2369 expanded)
%              Number of equality atoms :   76 ( 134 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2009,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f72,f77,f82,f166,f476,f1233,f1525,f2008])).

fof(f2008,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f2007])).

fof(f2007,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_22
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f1455,f1524])).

fof(f1524,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl8_26
  <=> m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1455,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1454,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl8_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1454,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_6
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1453,f81])).

fof(f81,plain,
    ( k11_lattice3(sK0,sK1,sK2) != k11_lattice3(sK0,sK2,sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_6
  <=> k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1453,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1449,f71])).

fof(f71,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1449,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_22 ),
    inference(superposition,[],[f879,f1232])).

fof(f1232,plain,
    ( k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f1230])).

fof(f1230,plain,
    ( spl8_22
  <=> k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f879,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f878,f84])).

fof(f84,plain,
    ( ! [X6,X5] :
        ( r1_orders_2(sK0,sK5(sK0,X5,X6),X6)
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
        | r1_orders_2(sK0,sK5(sK0,X5,X6),X6)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattice3)).

fof(f49,plain,
    ( v2_lattice3(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl8_2
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f878,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f876,f83])).

fof(f83,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,sK5(sK0,X3,X4),X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f63,f54])).

fof(f63,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,X3,X4),X3)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f876,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f872])).

fof(f872,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f699,f89])).

fof(f89,plain,
    ( ! [X4,X5,X3] :
        ( r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X3)
        | ~ r1_orders_2(sK0,X5,X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k11_lattice3(sK0,X3,X4) = X5 )
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
        | ~ r1_orders_2(sK0,X5,X3)
        | ~ r1_orders_2(sK0,X5,X4)
        | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4)
        | k11_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f60,f49])).

fof(f60,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X3)
        | ~ r1_orders_2(sK0,X5,X4)
        | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4)
        | k11_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f57,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f57,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,X3)
        | ~ r1_orders_2(sK0,X5,X4)
        | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4)
        | k11_lattice3(sK0,X3,X4) = X5 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f44,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl8_1
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f699,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f698,f49])).

fof(f698,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f697,f54])).

fof(f697,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f694])).

fof(f694,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f613,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f613,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f612,f84])).

fof(f612,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X1)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f495,f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = X2 )
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
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0)
        | k11_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f59,f49])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0)
        | k11_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0)
        | k11_lattice3(sK0,X0,X1) = X2 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f495,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | sK5(sK0,X3,X4) = k11_lattice3(sK0,X4,X5)
        | ~ r1_orders_2(sK0,sK5(sK0,X3,X4),X5) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X4)
        | ~ r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | sK5(sK0,X3,X4) = k11_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X3,X4),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f480,f84])).

fof(f480,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f479,f49])).

fof(f479,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f478,f54])).

fof(f478,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f165,f26])).

fof(f165,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_8
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1525,plain,
    ( spl8_26
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f1384,f1230,f74,f69,f52,f47,f1522])).

fof(f1384,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1383,f49])).

fof(f1383,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1382,f54])).

fof(f1382,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1381,f71])).

fof(f1381,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f1296,f76])).

fof(f1296,plain,
    ( m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl8_22 ),
    inference(superposition,[],[f26,f1232])).

fof(f1233,plain,
    ( spl8_22
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1123,f164,f74,f69,f52,f47,f42,f1230])).

fof(f1123,plain,
    ( k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(resolution,[],[f787,f76])).

fof(f787,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,sK2) = k11_lattice3(sK0,X0,sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f677,f71])).

fof(f677,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f676,f49])).

fof(f676,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f675,f54])).

fof(f675,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f673])).

fof(f673,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f632,f26])).

fof(f632,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f631,f83])).

fof(f631,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f630,f84])).

fof(f630,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f626,f87])).

fof(f626,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X2,X3)),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f622])).

fof(f622,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X2,X3)),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X2,X3),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f496,f89])).

fof(f496,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X0,X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X2),X1) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X2)
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k11_lattice3(sK0,X0,X1) = sK5(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(resolution,[],[f480,f83])).

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
    ( ~ v2_lattice3(sK0)
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
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f134,f54])).

fof(f134,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f133,f49])).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f132,f44])).

fof(f132,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X2)
        | ~ r1_orders_2(sK0,sK5(sK0,X0,X1),X3)
        | v2_struct_0(sK0)
        | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f108,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | v2_struct_0(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f108,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X3)
        | ~ r1_orders_2(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1)
        | ~ r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f94,f26])).

fof(f94,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X7)
        | ~ r1_orders_2(sK0,sK5(sK0,X5,X6),X4)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | sK5(sK0,X5,X6) = k11_lattice3(sK0,X7,X4)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,X7,X4,sK5(sK0,X5,X6)),X5)
        | ~ r1_orders_2(sK0,sK7(sK0,X7,X4,sK5(sK0,X5,X6)),X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f62,f54])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1)
        | r1_orders_2(sK0,X2,sK5(sK0,X0,X1))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X1)
      | ~ r1_orders_2(X0,X4,X2)
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X6)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k11_lattice3(sK0,X6,X7) = X8 )
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
        | ~ r1_orders_2(sK0,X8,X6)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8)
        | k11_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f61,f49])).

fof(f61,plain,
    ( ! [X6,X8,X7] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X6)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8)
        | k11_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f58,f20])).

fof(f58,plain,
    ( ! [X6,X8,X7] :
        ( v2_struct_0(sK0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X6)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8)
        | k11_lattice3(sK0,X6,X7) = X8 )
    | ~ spl8_1 ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f15,f79])).

fof(f15,plain,(
    k11_lattice3(sK0,sK1,sK2) != k11_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

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
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3638)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3638)Refutation not found, incomplete strategy% (3638)------------------------------
% 0.21/0.48  % (3638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3638)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3638)Memory used [KB]: 10618
% 0.21/0.48  % (3638)Time elapsed: 0.060 s
% 0.21/0.48  % (3638)------------------------------
% 0.21/0.48  % (3638)------------------------------
% 0.21/0.49  % (3646)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (3657)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (3644)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3640)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (3642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (3643)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (3652)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (3654)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (3645)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (3649)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3641)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (3657)Refutation not found, incomplete strategy% (3657)------------------------------
% 0.21/0.51  % (3657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3657)Memory used [KB]: 10618
% 0.21/0.51  % (3657)Time elapsed: 0.095 s
% 0.21/0.51  % (3657)------------------------------
% 0.21/0.51  % (3657)------------------------------
% 0.21/0.51  % (3651)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (3648)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (3639)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (3637)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (3655)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (3650)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (3647)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (3653)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (3656)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.58/0.59  % (3640)Refutation found. Thanks to Tanya!
% 1.58/0.59  % SZS status Theorem for theBenchmark
% 1.58/0.60  % SZS output start Proof for theBenchmark
% 1.58/0.60  fof(f2009,plain,(
% 1.58/0.60    $false),
% 1.58/0.60    inference(avatar_sat_refutation,[],[f45,f50,f55,f72,f77,f82,f166,f476,f1233,f1525,f2008])).
% 1.58/0.60  fof(f2008,plain,(
% 1.58/0.60    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_22 | ~spl8_26),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f2007])).
% 1.58/0.60  fof(f2007,plain,(
% 1.58/0.60    $false | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_22 | ~spl8_26)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1455,f1524])).
% 1.58/0.60  fof(f1524,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl8_26),
% 1.58/0.60    inference(avatar_component_clause,[],[f1522])).
% 1.58/0.60  fof(f1522,plain,(
% 1.58/0.60    spl8_26 <=> m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.58/0.60  fof(f1455,plain,(
% 1.58/0.60    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1454,f76])).
% 1.58/0.60  fof(f76,plain,(
% 1.58/0.60    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_5),
% 1.58/0.60    inference(avatar_component_clause,[],[f74])).
% 1.58/0.60  fof(f74,plain,(
% 1.58/0.60    spl8_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.58/0.60  fof(f1454,plain,(
% 1.58/0.60    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_6 | ~spl8_8 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1453,f81])).
% 1.58/0.60  fof(f81,plain,(
% 1.58/0.60    k11_lattice3(sK0,sK1,sK2) != k11_lattice3(sK0,sK2,sK1) | spl8_6),
% 1.58/0.60    inference(avatar_component_clause,[],[f79])).
% 1.58/0.60  fof(f79,plain,(
% 1.58/0.60    spl8_6 <=> k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.58/0.60  fof(f1453,plain,(
% 1.58/0.60    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1449,f71])).
% 1.58/0.60  fof(f71,plain,(
% 1.58/0.60    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl8_4),
% 1.58/0.60    inference(avatar_component_clause,[],[f69])).
% 1.58/0.60  fof(f69,plain,(
% 1.58/0.60    spl8_4 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.58/0.60  fof(f1449,plain,(
% 1.58/0.60    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8 | ~spl8_22)),
% 1.58/0.60    inference(superposition,[],[f879,f1232])).
% 1.58/0.60  fof(f1232,plain,(
% 1.58/0.60    k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2) | ~spl8_22),
% 1.58/0.60    inference(avatar_component_clause,[],[f1230])).
% 1.58/0.60  fof(f1230,plain,(
% 1.58/0.60    spl8_22 <=> k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.58/0.60  fof(f879,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f878,f84])).
% 1.58/0.60  fof(f84,plain,(
% 1.58/0.60    ( ! [X6,X5] : (r1_orders_2(sK0,sK5(sK0,X5,X6),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f64,f54])).
% 1.58/0.60  fof(f54,plain,(
% 1.58/0.60    l1_orders_2(sK0) | ~spl8_3),
% 1.58/0.60    inference(avatar_component_clause,[],[f52])).
% 1.58/0.60  fof(f52,plain,(
% 1.58/0.60    spl8_3 <=> l1_orders_2(sK0)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.58/0.60  fof(f64,plain,(
% 1.58/0.60    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,X5,X6),X6) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.58/0.60    inference(resolution,[],[f49,f28])).
% 1.58/0.60  fof(f28,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~l1_orders_2(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f11])).
% 1.58/0.60  fof(f11,plain,(
% 1.58/0.60    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.58/0.60    inference(flattening,[],[f10])).
% 1.58/0.60  fof(f10,plain,(
% 1.58/0.60    ! [X0] : ((v2_lattice3(X0) <=> ! [X1] : (! [X2] : (? [X3] : (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f2])).
% 1.58/0.60  fof(f2,axiom,(
% 1.58/0.60    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattice3)).
% 1.58/0.60  fof(f49,plain,(
% 1.58/0.60    v2_lattice3(sK0) | ~spl8_2),
% 1.58/0.60    inference(avatar_component_clause,[],[f47])).
% 1.58/0.60  fof(f47,plain,(
% 1.58/0.60    spl8_2 <=> v2_lattice3(sK0)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.58/0.60  fof(f878,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f876,f83])).
% 1.58/0.60  fof(f83,plain,(
% 1.58/0.60    ( ! [X4,X3] : (r1_orders_2(sK0,sK5(sK0,X3,X4),X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f63,f54])).
% 1.58/0.60  fof(f63,plain,(
% 1.58/0.60    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,X3,X4),X3) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.58/0.60    inference(resolution,[],[f49,f27])).
% 1.58/0.60  fof(f27,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,sK5(X0,X1,X2),X1) | ~l1_orders_2(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f11])).
% 1.58/0.60  fof(f876,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f872])).
% 1.58/0.60  fof(f872,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X2) = sK5(sK0,X2,X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f699,f89])).
% 1.58/0.60  fof(f89,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X3) | ~r1_orders_2(sK0,X5,X4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k11_lattice3(sK0,X3,X4) = X5) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f88,f54])).
% 1.58/0.60  fof(f88,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X3) | ~r1_orders_2(sK0,X5,X4) | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4) | k11_lattice3(sK0,X3,X4) = X5) ) | (~spl8_1 | ~spl8_2)),
% 1.58/0.60    inference(subsumption_resolution,[],[f60,f49])).
% 1.58/0.60  fof(f60,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X3) | ~r1_orders_2(sK0,X5,X4) | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4) | k11_lattice3(sK0,X3,X4) = X5) ) | ~spl8_1),
% 1.58/0.60    inference(subsumption_resolution,[],[f57,f20])).
% 1.58/0.60  fof(f20,plain,(
% 1.58/0.60    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f9])).
% 1.58/0.60  fof(f9,plain,(
% 1.58/0.60    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.58/0.60    inference(flattening,[],[f8])).
% 1.58/0.60  fof(f8,plain,(
% 1.58/0.60    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.58/0.60    inference(ennf_transformation,[],[f1])).
% 1.58/0.60  fof(f1,axiom,(
% 1.58/0.60    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).
% 1.58/0.60  fof(f57,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X3) | ~r1_orders_2(sK0,X5,X4) | r1_orders_2(sK0,sK7(sK0,X3,X4,X5),X4) | k11_lattice3(sK0,X3,X4) = X5) ) | ~spl8_1),
% 1.58/0.60    inference(resolution,[],[f44,f33])).
% 1.58/0.60  fof(f33,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK7(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3) )),
% 1.58/0.60    inference(cnf_transformation,[],[f13])).
% 1.58/0.60  fof(f13,plain,(
% 1.58/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.58/0.60    inference(flattening,[],[f12])).
% 1.58/0.60  fof(f12,plain,(
% 1.58/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f3])).
% 1.58/0.60  fof(f3,axiom,(
% 1.58/0.60    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 1.58/0.60  fof(f44,plain,(
% 1.58/0.60    v5_orders_2(sK0) | ~spl8_1),
% 1.58/0.60    inference(avatar_component_clause,[],[f42])).
% 1.58/0.60  fof(f42,plain,(
% 1.58/0.60    spl8_1 <=> v5_orders_2(sK0)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.58/0.60  fof(f699,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f698,f49])).
% 1.58/0.60  fof(f698,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f697,f54])).
% 1.58/0.60  fof(f697,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f694])).
% 1.58/0.60  fof(f694,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X2,X0)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X2,X0) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f613,f26])).
% 1.58/0.60  fof(f26,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f11])).
% 1.58/0.60  fof(f613,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f612,f84])).
% 1.58/0.60  fof(f612,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X1)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f606])).
% 1.58/0.60  fof(f606,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X1,X2,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X1) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X1,X2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f495,f87])).
% 1.58/0.60  fof(f87,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = X2) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f86,f54])).
% 1.58/0.60  fof(f86,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0) | k11_lattice3(sK0,X0,X1) = X2) ) | (~spl8_1 | ~spl8_2)),
% 1.58/0.60    inference(subsumption_resolution,[],[f59,f49])).
% 1.58/0.60  fof(f59,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0) | k11_lattice3(sK0,X0,X1) = X2) ) | ~spl8_1),
% 1.58/0.60    inference(subsumption_resolution,[],[f56,f20])).
% 1.58/0.60  fof(f56,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X0) | k11_lattice3(sK0,X0,X1) = X2) ) | ~spl8_1),
% 1.58/0.60    inference(resolution,[],[f44,f32])).
% 1.58/0.60  fof(f32,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK7(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3) )),
% 1.58/0.60    inference(cnf_transformation,[],[f13])).
% 1.58/0.60  fof(f495,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (~r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X3) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | sK5(sK0,X3,X4) = k11_lattice3(sK0,X4,X5) | ~r1_orders_2(sK0,sK5(sK0,X3,X4),X5)) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f493])).
% 1.58/0.60  fof(f493,plain,(
% 1.58/0.60    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X4) | ~r1_orders_2(sK0,sK7(sK0,X4,X5,sK5(sK0,X3,X4)),X3) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | sK5(sK0,X3,X4) = k11_lattice3(sK0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X3,X4),X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f480,f84])).
% 1.58/0.60  fof(f480,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3)) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f479,f49])).
% 1.58/0.60  fof(f479,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~v2_lattice3(sK0)) ) | (~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f478,f54])).
% 1.58/0.60  fof(f478,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | ~spl8_8),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f477])).
% 1.58/0.60  fof(f477,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | ~spl8_8),
% 1.58/0.60    inference(resolution,[],[f165,f26])).
% 1.58/0.60  fof(f165,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3)) ) | ~spl8_8),
% 1.58/0.60    inference(avatar_component_clause,[],[f164])).
% 1.58/0.60  fof(f164,plain,(
% 1.58/0.60    spl8_8 <=> ! [X1,X3,X0,X2] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3))),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.58/0.60  fof(f1525,plain,(
% 1.58/0.60    spl8_26 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_22),
% 1.58/0.60    inference(avatar_split_clause,[],[f1384,f1230,f74,f69,f52,f47,f1522])).
% 1.58/0.60  fof(f1384,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1383,f49])).
% 1.58/0.60  fof(f1383,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1382,f54])).
% 1.58/0.60  fof(f1382,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1381,f71])).
% 1.58/0.60  fof(f1381,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | (~spl8_5 | ~spl8_22)),
% 1.58/0.60    inference(subsumption_resolution,[],[f1296,f76])).
% 1.58/0.60  fof(f1296,plain,(
% 1.58/0.60    m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~spl8_22),
% 1.58/0.60    inference(superposition,[],[f26,f1232])).
% 1.58/0.60  fof(f1233,plain,(
% 1.58/0.60    spl8_22 | ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8),
% 1.58/0.60    inference(avatar_split_clause,[],[f1123,f164,f74,f69,f52,f47,f42,f1230])).
% 1.58/0.60  fof(f1123,plain,(
% 1.58/0.60    k11_lattice3(sK0,sK1,sK2) = sK5(sK0,sK1,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f787,f76])).
% 1.58/0.60  fof(f787,plain,(
% 1.58/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,sK2) = k11_lattice3(sK0,X0,sK2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f677,f71])).
% 1.58/0.60  fof(f677,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f676,f49])).
% 1.58/0.60  fof(f676,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f675,f54])).
% 1.58/0.60  fof(f675,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f673])).
% 1.58/0.60  fof(f673,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,X1,X0) = sK5(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f632,f26])).
% 1.58/0.60  fof(f632,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f631,f83])).
% 1.58/0.60  fof(f631,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f630,f84])).
% 1.58/0.60  fof(f630,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(subsumption_resolution,[],[f626,f87])).
% 1.58/0.60  fof(f626,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f622])).
% 1.58/0.60  fof(f622,plain,(
% 1.58/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X2,X3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X2) | ~r1_orders_2(sK0,sK5(sK0,X2,X3),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,X3) = k11_lattice3(sK0,X2,X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f496,f89])).
% 1.58/0.60  fof(f496,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X0,X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X2),X1)) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f492])).
% 1.58/0.60  fof(f492,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X2) | ~r1_orders_2(sK0,sK7(sK0,X0,X1,sK5(sK0,X0,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,X0,X1) = sK5(sK0,X0,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X2),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3 | ~spl8_8)),
% 1.58/0.60    inference(resolution,[],[f480,f83])).
% 1.58/0.60  fof(f476,plain,(
% 1.58/0.60    ~spl8_2 | ~spl8_3 | ~spl8_7),
% 1.58/0.60    inference(avatar_contradiction_clause,[],[f475])).
% 1.58/0.60  fof(f475,plain,(
% 1.58/0.60    $false | (~spl8_2 | ~spl8_3 | ~spl8_7)),
% 1.58/0.60    inference(subsumption_resolution,[],[f474,f54])).
% 1.58/0.60  fof(f474,plain,(
% 1.58/0.60    ~l1_orders_2(sK0) | (~spl8_2 | ~spl8_7)),
% 1.58/0.60    inference(subsumption_resolution,[],[f473,f49])).
% 1.58/0.60  fof(f473,plain,(
% 1.58/0.60    ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl8_7),
% 1.58/0.60    inference(resolution,[],[f162,f20])).
% 1.58/0.60  fof(f162,plain,(
% 1.58/0.60    v2_struct_0(sK0) | ~spl8_7),
% 1.58/0.60    inference(avatar_component_clause,[],[f160])).
% 1.58/0.60  fof(f160,plain,(
% 1.58/0.60    spl8_7 <=> v2_struct_0(sK0)),
% 1.58/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.58/0.60  fof(f166,plain,(
% 1.58/0.60    spl8_7 | spl8_8 | ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.58/0.60    inference(avatar_split_clause,[],[f135,f52,f47,f42,f164,f160])).
% 1.58/0.60  fof(f135,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f134,f54])).
% 1.58/0.60  fof(f134,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f133,f49])).
% 1.58/0.60  fof(f133,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f132,f44])).
% 1.58/0.60  fof(f132,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f131])).
% 1.58/0.60  fof(f131,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X0) | ~r1_orders_2(sK0,sK7(sK0,X2,X3,sK5(sK0,X0,X1)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X2) | ~r1_orders_2(sK0,sK5(sK0,X0,X1),X3) | v2_struct_0(sK0) | sK5(sK0,X0,X1) = k11_lattice3(sK0,X2,X3)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(resolution,[],[f108,f31])).
% 1.58/0.60  fof(f31,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | v2_struct_0(X0) | k11_lattice3(X0,X1,X2) = X3) )),
% 1.58/0.60    inference(cnf_transformation,[],[f13])).
% 1.58/0.60  fof(f108,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f107,f49])).
% 1.58/0.60  fof(f107,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f106,f54])).
% 1.58/0.60  fof(f106,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(duplicate_literal_removal,[],[f105])).
% 1.58/0.60  fof(f105,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X3) | ~r1_orders_2(sK0,sK5(sK0,X1,X2),X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK5(sK0,X1,X2) = k11_lattice3(sK0,X3,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X3,X0,sK5(sK0,X1,X2)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X1) | ~r1_orders_2(sK0,sK7(sK0,X3,X0,sK5(sK0,X1,X2)),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0)) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(resolution,[],[f94,f26])).
% 1.58/0.60  fof(f94,plain,(
% 1.58/0.60    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X7) | ~r1_orders_2(sK0,sK5(sK0,X5,X6),X4) | ~m1_subset_1(X7,u1_struct_0(sK0)) | sK5(sK0,X5,X6) = k11_lattice3(sK0,X7,X4) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X7,X4,sK5(sK0,X5,X6)),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK7(sK0,X7,X4,sK5(sK0,X5,X6)),X5) | ~r1_orders_2(sK0,sK7(sK0,X7,X4,sK5(sK0,X5,X6)),X6) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(resolution,[],[f91,f85])).
% 1.58/0.60  fof(f85,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f62,f54])).
% 1.58/0.60  fof(f62,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X2,X1) | r1_orders_2(sK0,X2,sK5(sK0,X0,X1)) | ~l1_orders_2(sK0)) ) | ~spl8_2),
% 1.58/0.60    inference(resolution,[],[f49,f25])).
% 1.58/0.60  fof(f25,plain,(
% 1.58/0.60    ( ! [X4,X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X4,X1) | ~r1_orders_2(X0,X4,X2) | r1_orders_2(X0,X4,sK5(X0,X1,X2)) | ~l1_orders_2(X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f11])).
% 1.58/0.60  fof(f91,plain,(
% 1.58/0.60    ( ! [X6,X8,X7] : (~r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X6) | ~r1_orders_2(sK0,X8,X7) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k11_lattice3(sK0,X6,X7) = X8) ) | (~spl8_1 | ~spl8_2 | ~spl8_3)),
% 1.58/0.60    inference(subsumption_resolution,[],[f90,f54])).
% 1.58/0.60  fof(f90,plain,(
% 1.58/0.60    ( ! [X6,X8,X7] : (~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X6) | ~r1_orders_2(sK0,X8,X7) | ~r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8) | k11_lattice3(sK0,X6,X7) = X8) ) | (~spl8_1 | ~spl8_2)),
% 1.58/0.60    inference(subsumption_resolution,[],[f61,f49])).
% 1.58/0.60  fof(f61,plain,(
% 1.58/0.60    ( ! [X6,X8,X7] : (~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X6) | ~r1_orders_2(sK0,X8,X7) | ~r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8) | k11_lattice3(sK0,X6,X7) = X8) ) | ~spl8_1),
% 1.58/0.60    inference(subsumption_resolution,[],[f58,f20])).
% 1.58/0.60  fof(f58,plain,(
% 1.58/0.60    ( ! [X6,X8,X7] : (v2_struct_0(sK0) | ~v2_lattice3(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,X6) | ~r1_orders_2(sK0,X8,X7) | ~r1_orders_2(sK0,sK7(sK0,X6,X7,X8),X8) | k11_lattice3(sK0,X6,X7) = X8) ) | ~spl8_1),
% 1.58/0.60    inference(resolution,[],[f44,f34])).
% 1.58/0.60  fof(f34,plain,(
% 1.58/0.60    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,sK7(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3) )),
% 1.58/0.60    inference(cnf_transformation,[],[f13])).
% 1.58/0.60  fof(f82,plain,(
% 1.58/0.60    ~spl8_6),
% 1.58/0.60    inference(avatar_split_clause,[],[f15,f79])).
% 1.58/0.60  fof(f15,plain,(
% 1.58/0.60    k11_lattice3(sK0,sK1,sK2) != k11_lattice3(sK0,sK2,sK1)),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  fof(f7,plain,(
% 1.58/0.60    ? [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0))),
% 1.58/0.60    inference(flattening,[],[f6])).
% 1.58/0.60  fof(f6,plain,(
% 1.58/0.60    ? [X0] : (? [X1] : (? [X2] : (k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)))),
% 1.58/0.60    inference(ennf_transformation,[],[f5])).
% 1.58/0.60  fof(f5,negated_conjecture,(
% 1.58/0.60    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 1.58/0.60    inference(negated_conjecture,[],[f4])).
% 1.58/0.60  fof(f4,conjecture,(
% 1.58/0.60    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).
% 1.58/0.60  fof(f77,plain,(
% 1.58/0.60    spl8_5),
% 1.58/0.60    inference(avatar_split_clause,[],[f16,f74])).
% 1.58/0.60  fof(f16,plain,(
% 1.58/0.60    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  fof(f72,plain,(
% 1.58/0.60    spl8_4),
% 1.58/0.60    inference(avatar_split_clause,[],[f14,f69])).
% 1.58/0.60  fof(f14,plain,(
% 1.58/0.60    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  fof(f55,plain,(
% 1.58/0.60    spl8_3),
% 1.58/0.60    inference(avatar_split_clause,[],[f19,f52])).
% 1.58/0.60  fof(f19,plain,(
% 1.58/0.60    l1_orders_2(sK0)),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  fof(f50,plain,(
% 1.58/0.60    spl8_2),
% 1.58/0.60    inference(avatar_split_clause,[],[f18,f47])).
% 1.58/0.60  fof(f18,plain,(
% 1.58/0.60    v2_lattice3(sK0)),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  fof(f45,plain,(
% 1.58/0.60    spl8_1),
% 1.58/0.60    inference(avatar_split_clause,[],[f17,f42])).
% 1.58/0.60  fof(f17,plain,(
% 1.58/0.60    v5_orders_2(sK0)),
% 1.58/0.60    inference(cnf_transformation,[],[f7])).
% 1.58/0.60  % SZS output end Proof for theBenchmark
% 1.58/0.60  % (3640)------------------------------
% 1.58/0.60  % (3640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (3640)Termination reason: Refutation
% 1.58/0.60  
% 1.58/0.60  % (3640)Memory used [KB]: 11769
% 1.58/0.60  % (3640)Time elapsed: 0.167 s
% 1.58/0.60  % (3640)------------------------------
% 1.58/0.60  % (3640)------------------------------
% 1.58/0.61  % (3636)Success in time 0.237 s
%------------------------------------------------------------------------------
