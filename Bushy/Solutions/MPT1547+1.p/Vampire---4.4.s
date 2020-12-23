%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t25_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 323 expanded)
%              Number of leaves         :   24 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  759 (1386 expanded)
%              Number of equality atoms :   50 (  92 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f97,f101,f139,f144,f185,f219,f222,f425,f699,f705,f706,f790,f859,f860])).

fof(f860,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k12_lattice3(sK0,sK2,sK1)
    | k12_lattice3(sK0,sK2,sK1) != sK1
    | k12_lattice3(sK0,sK1,sK2) = sK1 ),
    introduced(theory_axiom,[])).

fof(f859,plain,
    ( spl6_66
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f835,f788,f183,f179,f99,f95,f91,f87,f83,f692])).

fof(f692,plain,
    ( spl6_66
  <=> k12_lattice3(sK0,sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f83,plain,
    ( spl6_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f87,plain,
    ( spl6_4
  <=> v2_lattice3(sK0) ),
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

fof(f179,plain,
    ( spl6_20
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f183,plain,
    ( spl6_22
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f788,plain,
    ( spl6_72
  <=> r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f835,plain,
    ( k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f834,f84])).

fof(f84,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f834,plain,
    ( ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f833,f180])).

fof(f180,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f833,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f832,f184])).

fof(f184,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f832,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f831,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f831,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f830,f96])).

fof(f96,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f830,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f829,f92])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f829,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_4
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f828,f88])).

fof(f88,plain,
    ( v2_lattice3(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f828,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_72 ),
    inference(duplicate_literal_removal,[],[f823])).

fof(f823,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v5_orders_2(sK0)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_72 ),
    inference(resolution,[],[f789,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',t23_yellow_0)).

fof(f789,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f788])).

fof(f790,plain,
    ( spl6_72
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | spl6_17
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f779,f423,f183,f179,f213,f99,f95,f91,f87,f83,f788])).

fof(f213,plain,
    ( spl6_17
  <=> k12_lattice3(sK0,sK1,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f423,plain,
    ( spl6_50
  <=> k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f779,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f778,f214])).

fof(f214,plain,
    ( k12_lattice3(sK0,sK1,sK2) != sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f213])).

fof(f778,plain,
    ( k12_lattice3(sK0,sK1,sK2) = sK1
    | r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f777,f424])).

fof(f424,plain,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f423])).

fof(f777,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f776,f100])).

fof(f776,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK1,sK1),sK1)
    | k12_lattice3(sK0,sK2,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(resolution,[],[f241,f180])).

fof(f241,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f240,f84])).

fof(f240,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X2)
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f239,f100])).

fof(f239,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X2)
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f238,f96])).

fof(f238,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X2)
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f237,f92])).

fof(f237,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X2)
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f225,f88])).

fof(f225,plain,
    ( ! [X2] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK1,X2)
        | r1_orders_2(sK0,sK5(sK0,sK2,X2,sK1),X2)
        | k12_lattice3(sK0,sK2,X2) = sK1 )
    | ~ spl6_22 ),
    inference(resolution,[],[f184,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,X1)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
      | k12_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f706,plain,
    ( spl6_14
    | spl6_20
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f702,f217,f99,f91,f79,f179,f130])).

fof(f130,plain,
    ( spl6_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f79,plain,
    ( spl6_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f217,plain,
    ( spl6_24
  <=> r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f702,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f701,f100])).

fof(f701,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f700,f92])).

fof(f700,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f221,f80])).

fof(f80,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f221,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_24 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl6_24 ),
    inference(resolution,[],[f218,f55])).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',redefinition_r3_orders_2)).

fof(f218,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f705,plain,
    ( ~ spl6_17
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f703,f137,f213])).

fof(f137,plain,
    ( spl6_18
  <=> r3_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f703,plain,
    ( k12_lattice3(sK0,sK1,sK2) != sK1
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f47,f138])).

fof(f138,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f47,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | k12_lattice3(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',t25_yellow_0)).

fof(f699,plain,
    ( spl6_14
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | spl6_19
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f698,f183,f146,f99,f95,f91,f79,f130])).

fof(f146,plain,
    ( spl6_19
  <=> ~ r3_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f698,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f697,f147])).

fof(f147,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f697,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f696,f96])).

fof(f696,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f695,f100])).

fof(f695,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f694,f92])).

fof(f694,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_0
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f226,f80])).

fof(f226,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ spl6_22 ),
    inference(resolution,[],[f184,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f425,plain,
    ( spl6_50
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f290,f99,f95,f91,f87,f83,f423])).

fof(f290,plain,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f111,f100])).

fof(f111,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,sK2) = k12_lattice3(sK0,sK2,X1) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f110,f84])).

fof(f110,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,sK2) = k12_lattice3(sK0,sK2,X1) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f109,f92])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,sK2) = k12_lattice3(sK0,sK2,X1) )
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f103,f88])).

fof(f103,plain,
    ( ! [X1] :
        ( ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,sK2) = k12_lattice3(sK0,sK2,X1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',commutativity_k12_lattice3)).

fof(f222,plain,
    ( spl6_14
    | spl6_22
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f191,f137,f99,f95,f91,f79,f183,f130])).

fof(f191,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f190,f96])).

fof(f190,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f189,f100])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f188,f92])).

fof(f188,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f187,f80])).

fof(f187,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl6_18 ),
    inference(resolution,[],[f138,f55])).

fof(f219,plain,
    ( spl6_24
    | spl6_14
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f125,f99,f91,f79,f130,f217])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f124,f92])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f116,f80])).

fof(f116,plain,
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
    inference(condensation,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',reflexivity_r3_orders_2)).

fof(f185,plain,
    ( spl6_22
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f172,f134,f99,f95,f91,f87,f83,f183])).

fof(f134,plain,
    ( spl6_16
  <=> k12_lattice3(sK0,sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f172,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f171,f135])).

fof(f135,plain,
    ( k12_lattice3(sK0,sK1,sK2) = sK1
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f171,plain,
    ( r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f170,f84])).

fof(f170,plain,
    ( ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f169,f96])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f168,f92])).

fof(f168,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f167,f88])).

fof(f167,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f152,f100])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_16 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl6_16 ),
    inference(superposition,[],[f74,f135])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

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
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f131,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t25_yellow_0.p',cc2_lattice3)).

fof(f131,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f139,plain,
    ( spl6_16
    | spl6_18 ),
    inference(avatar_split_clause,[],[f46,f137,f134])).

fof(f46,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | k12_lattice3(sK0,sK1,sK2) = sK1 ),
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
    v2_lattice3(sK0) ),
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
