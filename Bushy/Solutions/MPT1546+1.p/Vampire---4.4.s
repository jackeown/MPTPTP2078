%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t24_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 278 expanded)
%              Number of leaves         :   23 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  660 (1230 expanded)
%              Number of equality atoms :   49 (  97 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f794,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f97,f101,f139,f144,f174,f202,f211,f263,f438,f713,f792,f793])).

fof(f793,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k13_lattice3(sK0,sK2,sK1)
    | k13_lattice3(sK0,sK2,sK1) != sK1
    | k13_lattice3(sK0,sK1,sK2) = sK1 ),
    introduced(theory_axiom,[])).

fof(f792,plain,
    ( spl6_70
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f765,f711,f261,f137,f99,f95,f91,f87,f83,f790])).

fof(f790,plain,
    ( spl6_70
  <=> k13_lattice3(sK0,sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f83,plain,
    ( spl6_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f87,plain,
    ( spl6_4
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f91,plain,
    ( spl6_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f95,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f99,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f137,plain,
    ( spl6_18
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f261,plain,
    ( spl6_30
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f711,plain,
    ( spl6_66
  <=> r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f765,plain,
    ( k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f764,f84])).

fof(f84,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f764,plain,
    ( ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f763,f262])).

fof(f262,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f261])).

fof(f763,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f762,f138])).

fof(f138,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f762,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f761,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f761,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f760,f96])).

fof(f96,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f760,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f759,f92])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f759,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f758,f88])).

fof(f88,plain,
    ( v1_lattice3(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f758,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_66 ),
    inference(duplicate_literal_removal,[],[f753])).

fof(f753,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_66 ),
    inference(resolution,[],[f712,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',t22_yellow_0)).

fof(f712,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f711])).

fof(f713,plain,
    ( spl6_66
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | spl6_17
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f316,f261,f137,f200,f99,f95,f91,f87,f83,f711])).

fof(f200,plain,
    ( spl6_17
  <=> k13_lattice3(sK0,sK1,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f316,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f315,f201])).

fof(f201,plain,
    ( k13_lattice3(sK0,sK1,sK2) != sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f315,plain,
    ( k13_lattice3(sK0,sK1,sK2) = sK1
    | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f314,f266])).

fof(f266,plain,
    ( k13_lattice3(sK0,sK1,sK2) = k13_lattice3(sK0,sK2,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f113,f100])).

fof(f113,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k13_lattice3(sK0,X1,sK2) = k13_lattice3(sK0,sK2,X1) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k13_lattice3(sK0,X1,sK2) = k13_lattice3(sK0,sK2,X1) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f111,f92])).

fof(f111,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k13_lattice3(sK0,X1,sK2) = k13_lattice3(sK0,sK2,X1) )
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f104,f88])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k13_lattice3(sK0,X1,sK2) = k13_lattice3(sK0,sK2,X1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f96,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',commutativity_k13_lattice3)).

fof(f314,plain,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f313,f100])).

fof(f313,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3(sK0,sK2,sK1,sK1))
    | k13_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(resolution,[],[f194,f262])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f193,f84])).

fof(f193,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,X2,sK1)
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f192,f100])).

fof(f192,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,X2,sK1)
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f191,f96])).

fof(f191,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,X2,sK1)
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f190,f92])).

fof(f190,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,X2,sK1)
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f178,f88])).

fof(f178,plain,
    ( ! [X2] :
        ( ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,X2,sK1)
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK1))
        | k13_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_18 ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X3)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f438,plain,
    ( spl6_48
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f266,f99,f95,f91,f87,f83,f436])).

fof(f436,plain,
    ( spl6_48
  <=> k13_lattice3(sK0,sK1,sK2) = k13_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f263,plain,
    ( spl6_14
    | spl6_30
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f216,f209,f99,f91,f79,f261,f130])).

fof(f130,plain,
    ( spl6_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f79,plain,
    ( spl6_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f209,plain,
    ( spl6_20
  <=> r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f216,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f215,f100])).

fof(f215,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f214,f92])).

fof(f214,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f213,f80])).

fof(f80,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f213,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_20 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_20 ),
    inference(resolution,[],[f210,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',redefinition_r3_orders_2)).

fof(f210,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl6_20
    | spl6_14
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f119,f99,f91,f79,f130,f209])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f118,f92])).

fof(f118,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f114,f80])).

fof(f114,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f100,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | r3_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',reflexivity_r3_orders_2)).

fof(f202,plain,
    ( ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f175,f137,f200])).

fof(f175,plain,
    ( k13_lattice3(sK0,sK1,sK2) != sK1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f47,f138])).

fof(f47,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | k13_lattice3(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',t24_yellow_0)).

fof(f174,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f172,f147])).

fof(f147,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_19
  <=> ~ r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f172,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f171,f135])).

fof(f135,plain,
    ( k13_lattice3(sK0,sK1,sK2) = sK1
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_16
  <=> k13_lattice3(sK0,sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f171,plain,
    ( r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f170,f84])).

fof(f170,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f169,f96])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f168,f92])).

fof(f168,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f167,f88])).

fof(f167,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f152,f100])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_16 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,sK2,k13_lattice3(sK0,sK1,sK2))
    | ~ spl6_16 ),
    inference(superposition,[],[f74,f135])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f144,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f142,f92])).

fof(f142,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f141,f88])).

fof(f141,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t24_yellow_0.p',cc1_lattice3)).

fof(f131,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f139,plain,
    ( spl6_16
    | spl6_18 ),
    inference(avatar_split_clause,[],[f46,f137,f134])).

fof(f46,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | k13_lattice3(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f53,f91])).

fof(f53,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f51,f83])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f50,f79])).

fof(f50,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
