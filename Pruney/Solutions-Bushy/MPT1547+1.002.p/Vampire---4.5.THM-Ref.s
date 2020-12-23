%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1547+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 263 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  675 (1214 expanded)
%              Number of equality atoms :   28 (  66 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f425,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f75,f80,f89,f98,f219,f231,f357,f389,f392,f408,f414,f424])).

fof(f424,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_17 ),
    inference(subsumption_resolution,[],[f420,f387])).

fof(f387,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl4_17
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f420,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f419,f52])).

fof(f52,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f419,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f418,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f418,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f417,f62])).

fof(f62,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f417,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f416,f57])).

fof(f57,plain,
    ( v2_lattice3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_3
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f416,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f404,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f404,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_7 ),
    inference(superposition,[],[f40,f84])).

fof(f84,plain,
    ( sK1 = k12_lattice3(sK0,sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_7
  <=> sK1 = k12_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f414,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8
    | spl4_10
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8
    | spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f412,f79])).

fof(f412,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | spl4_8
    | spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f411,f388])).

fof(f388,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f386])).

fof(f411,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | spl4_8
    | spl4_10 ),
    inference(subsumption_resolution,[],[f410,f74])).

fof(f410,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | spl4_8
    | spl4_10 ),
    inference(resolution,[],[f87,f368])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_1
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f353,f96])).

fof(f96,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f64,f62])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f47,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_8
  <=> r3_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f408,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f396,f84])).

fof(f396,plain,
    ( sK1 != k12_lattice3(sK0,sK1,sK2)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f21,f88])).

fof(f88,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f21,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | sK1 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k12_lattice3(X0,X1,X2) = X1
                <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f392,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f390,f388])).

fof(f390,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f236,f172])).

fof(f172,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_12
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f236,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f235,f74])).

fof(f235,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f234,f83])).

fof(f83,plain,
    ( sK1 != k12_lattice3(sK0,sK1,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f234,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f201,f79])).

fof(f201,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k12_lattice3(sK0,sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f135,f121])).

fof(f121,plain,
    ( ! [X4,X2,X3] :
        ( r1_orders_2(sK0,sK3(sK0,X2,X3,X4),X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k12_lattice3(sK0,X2,X3) = X4 )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f120,f62])).

fof(f120,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | r1_orders_2(sK0,sK3(sK0,X2,X3,X4),X2)
        | k12_lattice3(sK0,X2,X3) = X4 )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f68,f57])).

fof(f68,plain,
    ( ! [X4,X2,X3] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X2)
        | ~ r1_orders_2(sK0,X4,X3)
        | r1_orders_2(sK0,sK3(sK0,X2,X3,X4),X2)
        | k12_lattice3(sK0,X2,X3) = X4 )
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | k12_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK2,X4),X4)
        | ~ r1_orders_2(sK0,X4,sK1)
        | ~ r1_orders_2(sK0,X4,sK2)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k12_lattice3(sK0,sK1,sK2) = X4 )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f127,f74])).

fof(f127,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK1)
        | ~ r1_orders_2(sK0,X5,X4)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,X4,X5),X5)
        | k12_lattice3(sK0,sK1,X4) = X5 )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f125,f79])).

fof(f125,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK3(sK0,X8,X9,X10),X10)
        | k12_lattice3(sK0,X8,X9) = X10 )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( ! [X10,X8,X9] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK3(sK0,X8,X9,X10),X10)
        | k12_lattice3(sK0,X8,X9) = X10 )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f70,f57])).

fof(f70,plain,
    ( ! [X10,X8,X9] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X8)
        | ~ r1_orders_2(sK0,X10,X9)
        | ~ r1_orders_2(sK0,sK3(sK0,X8,X9,X10),X10)
        | k12_lattice3(sK0,X8,X9) = X10 )
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | k12_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f389,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_10 ),
    inference(avatar_split_clause,[],[f365,f95,f86,f77,f72,f60,f45,f386])).

fof(f365,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | spl4_10 ),
    inference(subsumption_resolution,[],[f364,f79])).

fof(f364,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8
    | spl4_10 ),
    inference(subsumption_resolution,[],[f359,f74])).

fof(f359,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_8
    | spl4_10 ),
    inference(resolution,[],[f358,f88])).

fof(f358,plain,
    ( ! [X2,X3] :
        ( ~ r3_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl4_1
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f352,f96])).

fof(f352,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f65,f62])).

fof(f65,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl4_1 ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f357,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f355,f62])).

fof(f355,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f354,f57])).

fof(f354,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f97,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f97,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f231,plain,
    ( ~ spl4_6
    | ~ spl4_9
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9
    | spl4_13 ),
    inference(subsumption_resolution,[],[f227,f79])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_9
    | spl4_13 ),
    inference(resolution,[],[f218,f93])).

fof(f93,plain,
    ( ! [X4] :
        ( r3_orders_2(sK0,X4,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_9
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_orders_2(sK0,X4,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f218,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_13
  <=> r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f219,plain,
    ( ~ spl4_13
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | spl4_10
    | spl4_12 ),
    inference(avatar_split_clause,[],[f184,f171,f95,f77,f60,f45,f216])).

fof(f184,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | spl4_10
    | spl4_12 ),
    inference(subsumption_resolution,[],[f183,f79])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK1,sK1)
    | ~ spl4_1
    | ~ spl4_4
    | spl4_10
    | spl4_12 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK1,sK1)
    | ~ spl4_1
    | ~ spl4_4
    | spl4_10
    | spl4_12 ),
    inference(resolution,[],[f173,f119])).

fof(f119,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl4_1
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f118,plain,
    ( ! [X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X3)
        | ~ r3_orders_2(sK0,X2,X3) )
    | ~ spl4_1
    | spl4_10 ),
    inference(subsumption_resolution,[],[f65,f96])).

fof(f173,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f98,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f90,f60,f45,f95,f92])).

fof(f90,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_orders_2(sK0,X4,X4) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f66,f62])).

fof(f66,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_orders_2(sK0,X4,X4) )
    | ~ spl4_1 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(condensation,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f89,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f20,f86,f82])).

fof(f20,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f77])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
