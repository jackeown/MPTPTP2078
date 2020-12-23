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
% DateTime   : Thu Dec  3 13:15:39 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  298 ( 852 expanded)
%              Number of leaves         :   41 ( 319 expanded)
%              Depth                    :   20
%              Number of atoms          : 1744 (3651 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f122,f128,f156,f161,f166,f171,f188,f191,f196,f265,f270,f293,f304,f318,f469,f595,f907,f925,f1122,f1196,f1203,f1468,f1473,f1698,f1728,f1736])).

fof(f1736,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_37
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f1735])).

fof(f1735,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_37
    | spl6_41 ),
    inference(subsumption_resolution,[],[f1734,f1466])).

fof(f1466,plain,
    ( r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f1465])).

fof(f1465,plain,
    ( spl6_37
  <=> r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1734,plain,
    ( ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_41 ),
    inference(subsumption_resolution,[],[f1733,f121])).

fof(f121,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1733,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_41 ),
    inference(resolution,[],[f1727,f211])).

fof(f211,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(sK5(X4,sK0,X3,X5),X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f113,f93])).

fof(f93,plain,
    ( l3_lattices(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f113,plain,
    ( ! [X4,X5,X3] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(sK5(X4,sK0,X3,X5),X5)
        | ~ r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f112,f78])).

fof(f78,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f112,plain,
    ( ! [X4,X5,X3] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(sK5(X4,sK0,X3,X5),X5)
        | ~ r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5)) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f107,f83])).

fof(f83,plain,
    ( v10_lattices(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f107,plain,
    ( ! [X4,X5,X3] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(sK5(X4,sK0,X3,X5),X5)
        | ~ r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f88,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_4_lattice3)).

fof(f88,plain,
    ( v4_lattice3(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1727,plain,
    ( ~ r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f1725])).

fof(f1725,plain,
    ( spl6_41
  <=> r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1728,plain,
    ( ~ spl6_41
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_35
    | spl6_40 ),
    inference(avatar_split_clause,[],[f1719,f1695,f1447,f153,f149,f145,f91,f86,f81,f76,f1725])).

fof(f145,plain,
    ( spl6_8
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f149,plain,
    ( spl6_9
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f153,plain,
    ( spl6_10
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1447,plain,
    ( spl6_35
  <=> m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f1695,plain,
    ( spl6_40
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f1719,plain,
    ( ~ r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_35
    | spl6_40 ),
    inference(subsumption_resolution,[],[f1716,f1448])).

fof(f1448,plain,
    ( m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1716,plain,
    ( ~ m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_40 ),
    inference(resolution,[],[f1697,f218])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f217,f123])).

fof(f123,plain,
    ( ! [X10] : m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f99,f93])).

fof(f99,plain,
    ( ! [X10] :
        ( ~ l3_lattices(sK0)
        | m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0)) )
    | spl6_1 ),
    inference(resolution,[],[f78,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | r3_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | r3_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f215,f176])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f175,f123])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | r1_lattices(sK0,k16_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f174,f138])).

fof(f138,plain,
    ( ! [X2] : r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f137,f78])).

fof(f137,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f136,f93])).

fof(f136,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f135,f88])).

fof(f135,plain,
    ( ! [X2] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f130,f83])).

fof(f130,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f123,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f174,plain,
    ( ! [X4,X5,X3] :
        ( ~ r3_lattice3(sK0,X3,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,X5)
        | r1_lattices(sK0,X3,X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f96,f93])).

fof(f96,plain,
    ( ! [X4,X5,X3] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,X5)
        | r1_lattices(sK0,X3,X4)
        | ~ r3_lattice3(sK0,X3,X5) )
    | spl6_1 ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f215,plain,
    ( ! [X14,X13] :
        ( ~ r1_lattices(sK0,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f214,f93])).

fof(f214,plain,
    ( ! [X14,X13] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X13,X14)
        | r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f213,f146])).

fof(f146,plain,
    ( v9_lattices(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f213,plain,
    ( ! [X14,X13] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X13,X14)
        | r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f212,f150])).

fof(f150,plain,
    ( v8_lattices(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f212,plain,
    ( ! [X14,X13] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X13,X14)
        | r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f101,f154])).

fof(f154,plain,
    ( v6_lattices(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f101,plain,
    ( ! [X14,X13] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X13,X14)
        | r3_lattices(sK0,X13,X14) )
    | spl6_1 ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f1697,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f1698,plain,
    ( ~ spl6_40
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_19
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f1691,f1447,f592,f315,f153,f149,f145,f119,f91,f81,f76,f1695])).

fof(f315,plain,
    ( spl6_19
  <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f592,plain,
    ( spl6_24
  <=> sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1691,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_19
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f1690,f317])).

fof(f317,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f315])).

fof(f1690,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f1689,f123])).

fof(f1689,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(duplicate_literal_removal,[],[f1687])).

fof(f1687,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(resolution,[],[f1686,f308])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f307,f78])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f306,f93])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f305])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f226,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(resolution,[],[f222,f172])).

fof(f172,plain,
    ( ! [X8,X9] :
        ( ~ r1_lattices(sK0,X8,sK4(sK0,X8,X9))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r3_lattice3(sK0,X8,X9) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f98,f93])).

fof(f98,plain,
    ( ! [X8,X9] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X8,sK4(sK0,X8,X9))
        | r3_lattice3(sK0,X8,X9) )
    | spl6_1 ),
    inference(resolution,[],[f78,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f222,plain,
    ( ! [X15,X16] :
        ( r1_lattices(sK0,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X15,X16) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f221,f93])).

fof(f221,plain,
    ( ! [X15,X16] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r1_lattices(sK0,X15,X16)
        | ~ r3_lattices(sK0,X15,X16) )
    | spl6_1
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f220,f146])).

fof(f220,plain,
    ( ! [X15,X16] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r1_lattices(sK0,X15,X16)
        | ~ r3_lattices(sK0,X15,X16) )
    | spl6_1
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f219,f150])).

fof(f219,plain,
    ( ! [X15,X16] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r1_lattices(sK0,X15,X16)
        | ~ r3_lattices(sK0,X15,X16) )
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f102,f154])).

fof(f102,plain,
    ( ! [X15,X16] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | r1_lattices(sK0,X15,X16)
        | ~ r3_lattices(sK0,X15,X16) )
    | spl6_1 ),
    inference(resolution,[],[f78,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1686,plain,
    ( ! [X1] :
        ( r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_24
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f823,f1448])).

fof(f823,plain,
    ( ! [X1] :
        ( r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f815,f121])).

fof(f815,plain,
    ( ! [X1] :
        ( r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(superposition,[],[f241,f594])).

fof(f594,plain,
    ( sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f592])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f105,f93])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1)) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f104,f78])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,X1,k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_lattices(X0,X1,X2)
                   => r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_filter_0)).

fof(f1473,plain,
    ( spl6_1
    | ~ spl6_4
    | spl6_19
    | spl6_37 ),
    inference(avatar_contradiction_clause,[],[f1472])).

fof(f1472,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | spl6_19
    | spl6_37 ),
    inference(subsumption_resolution,[],[f1471,f317])).

fof(f1471,plain,
    ( r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | spl6_37 ),
    inference(subsumption_resolution,[],[f1470,f123])).

fof(f1470,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | spl6_37 ),
    inference(resolution,[],[f1467,f139])).

fof(f139,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK4(sK0,X6,X7),X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattice3(sK0,X6,X7) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f97,f93])).

fof(f97,plain,
    ( ! [X6,X7] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,X6,X7),X7)
        | r3_lattice3(sK0,X6,X7) )
    | spl6_1 ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1467,plain,
    ( ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f1465])).

fof(f1468,plain,
    ( ~ spl6_37
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_35 ),
    inference(avatar_split_clause,[],[f1459,f1447,f119,f91,f86,f81,f76,f1465])).

fof(f1459,plain,
    ( ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_35 ),
    inference(subsumption_resolution,[],[f1458,f78])).

fof(f1458,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_35 ),
    inference(subsumption_resolution,[],[f1457,f121])).

fof(f1457,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_35 ),
    inference(subsumption_resolution,[],[f1456,f93])).

fof(f1456,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | spl6_35 ),
    inference(subsumption_resolution,[],[f1455,f88])).

fof(f1455,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | spl6_35 ),
    inference(subsumption_resolution,[],[f1454,f83])).

fof(f1454,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_35 ),
    inference(resolution,[],[f1449,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1449,plain,
    ( ~ m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1203,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f1202])).

fof(f1202,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7
    | spl6_34 ),
    inference(subsumption_resolution,[],[f1197,f121])).

fof(f1197,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_7
    | spl6_34 ),
    inference(resolution,[],[f1195,f143])).

fof(f143,plain,
    ( ! [X17] :
        ( r3_lattices(sK0,X17,X17)
        | ~ m1_subset_1(X17,u1_struct_0(sK0)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_7
  <=> ! [X17] :
        ( ~ m1_subset_1(X17,u1_struct_0(sK0))
        | r3_lattices(sK0,X17,X17) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1195,plain,
    ( ~ r3_lattices(sK0,sK1,sK1)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1193,plain,
    ( spl6_34
  <=> r3_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1196,plain,
    ( ~ spl6_34
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_18
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f1189,f905,f301,f153,f149,f145,f119,f91,f76,f1193])).

fof(f301,plain,
    ( spl6_18
  <=> r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f905,plain,
    ( spl6_29
  <=> ! [X4] :
        ( r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f1189,plain,
    ( ~ r3_lattices(sK0,sK1,sK1)
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_18
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1188,f303])).

fof(f303,plain,
    ( ~ r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f301])).

fof(f1188,plain,
    ( ~ r3_lattices(sK0,sK1,sK1)
    | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1187,f121])).

fof(f1187,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,sK1,sK1)
    | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(duplicate_literal_removal,[],[f1185])).

fof(f1185,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(resolution,[],[f906,f308])).

fof(f906,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,sK1) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f905])).

fof(f1122,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_18
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f1121])).

fof(f1121,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_18
    | spl6_30 ),
    inference(subsumption_resolution,[],[f1099,f303])).

fof(f1099,plain,
    ( r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_30 ),
    inference(subsumption_resolution,[],[f941,f121])).

fof(f941,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_4
    | spl6_30 ),
    inference(resolution,[],[f924,f139])).

fof(f924,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl6_30
  <=> r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f925,plain,
    ( ~ spl6_30
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_28 ),
    inference(avatar_split_clause,[],[f913,f901,f119,f91,f86,f81,f76,f922])).

fof(f901,plain,
    ( spl6_28
  <=> m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f913,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_28 ),
    inference(subsumption_resolution,[],[f912,f78])).

fof(f912,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_28 ),
    inference(subsumption_resolution,[],[f911,f121])).

fof(f911,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_28 ),
    inference(subsumption_resolution,[],[f910,f93])).

fof(f910,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | spl6_28 ),
    inference(subsumption_resolution,[],[f909,f88])).

fof(f909,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ spl6_2
    | spl6_28 ),
    inference(subsumption_resolution,[],[f908,f83])).

fof(f908,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_28 ),
    inference(resolution,[],[f903,f67])).

fof(f903,plain,
    ( ~ m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f901])).

fof(f907,plain,
    ( ~ spl6_28
    | spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f623,f466,f178,f119,f91,f81,f76,f905,f901])).

fof(f178,plain,
    ( spl6_11
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f466,plain,
    ( spl6_23
  <=> sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f623,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f615,f121])).

fof(f615,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_23 ),
    inference(superposition,[],[f251,f468])).

fof(f468,plain,
    ( sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f466])).

fof(f251,plain,
    ( ! [X4,X5,X3] :
        ( r3_lattices(sK0,X5,k3_lattices(sK0,X4,X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X4,X5,X3] :
        ( r3_lattices(sK0,X5,k3_lattices(sK0,X4,X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(superposition,[],[f241,f179])).

fof(f179,plain,
    ( ! [X12,X11] :
        ( k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f595,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(avatar_split_clause,[],[f352,f315,f119,f91,f86,f81,f76,f592])).

fof(f352,plain,
    ( sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(subsumption_resolution,[],[f351,f123])).

fof(f351,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_19 ),
    inference(subsumption_resolution,[],[f347,f121])).

fof(f347,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_19 ),
    inference(resolution,[],[f229,f317])).

fof(f229,plain,
    ( ! [X4,X5,X3] :
        ( r3_lattice3(sK0,X4,a_3_4_lattice3(sK0,X3,X5))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | sK4(sK0,X4,a_3_4_lattice3(sK0,X3,X5)) = k3_lattices(sK0,X3,sK5(sK4(sK0,X4,a_3_4_lattice3(sK0,X3,X5)),sK0,X3,X5)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(resolution,[],[f227,f139])).

fof(f227,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))
        | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f111,f93])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f110,f78])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f106,f83])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f469,plain,
    ( spl6_23
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_18 ),
    inference(avatar_split_clause,[],[f350,f301,f119,f91,f86,f81,f76,f466])).

fof(f350,plain,
    ( sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f348,f121])).

fof(f348,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_18 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_18 ),
    inference(resolution,[],[f229,f303])).

fof(f318,plain,
    ( ~ spl6_19
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_16 ),
    inference(avatar_split_clause,[],[f299,f286,f91,f86,f81,f76,f315])).

fof(f286,plain,
    ( spl6_16
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f299,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_16 ),
    inference(subsumption_resolution,[],[f297,f123])).

fof(f297,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_16 ),
    inference(resolution,[],[f288,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f133,f78])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f132,f93])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f131,f88])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f129,f83])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f123,f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f288,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f286])).

fof(f304,plain,
    ( ~ spl6_18
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_17 ),
    inference(avatar_split_clause,[],[f295,f290,f119,f91,f86,f81,f76,f301])).

fof(f290,plain,
    ( spl6_17
  <=> r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f295,plain,
    ( ~ r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_17 ),
    inference(subsumption_resolution,[],[f294,f121])).

fof(f294,plain,
    ( ~ r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_17 ),
    inference(resolution,[],[f292,f134])).

fof(f292,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f290])).

fof(f293,plain,
    ( ~ spl6_16
    | ~ spl6_17
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f284,f259,f125,f119,f91,f76,f290,f286])).

fof(f125,plain,
    ( spl6_6
  <=> r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f259,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)
        | ~ r3_lattices(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f284,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f283,f123])).

fof(f283,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f282,f123])).

fof(f282,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | ~ m1_subset_1(k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | ~ spl6_5
    | spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f277,f121])).

fof(f277,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | ~ m1_subset_1(k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_6
    | ~ spl6_14 ),
    inference(resolution,[],[f260,f127])).

fof(f127,plain,
    ( ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f260,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f259])).

fof(f270,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_15 ),
    inference(subsumption_resolution,[],[f268,f93])).

fof(f268,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_15 ),
    inference(subsumption_resolution,[],[f267,f83])).

fof(f267,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_15 ),
    inference(subsumption_resolution,[],[f266,f78])).

fof(f266,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_15 ),
    inference(resolution,[],[f264,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f264,plain,
    ( ~ v5_lattices(sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_15
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f265,plain,
    ( spl6_14
    | ~ spl6_15
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f257,f185,f153,f149,f145,f91,f76,f262,f259])).

fof(f185,plain,
    ( spl6_13
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f256,f93])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f255,f146])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f254,f150])).

fof(f254,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f253,f154])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f95,f186])).

fof(f186,plain,
    ( v4_lattices(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f95,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_lattices(sK0)
        | ~ v5_lattices(sK0)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X2)
        | ~ r3_lattices(sK0,X1,X2)
        | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) )
    | spl6_1 ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X1,X3)
      | ~ r3_lattices(X0,X2,X3)
      | r3_lattices(X0,k3_lattices(X0,X1,X2),X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X1,X2),X3)
                  | ~ r3_lattices(X0,X2,X3)
                  | ~ r3_lattices(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X1,X2),X3)
                  | ~ r3_lattices(X0,X2,X3)
                  | ~ r3_lattices(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_lattices(X0,X2,X3)
                      & r3_lattices(X0,X1,X3) )
                   => r3_lattices(X0,k3_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_0)).

fof(f196,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_13 ),
    inference(subsumption_resolution,[],[f194,f93])).

fof(f194,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_13 ),
    inference(subsumption_resolution,[],[f193,f83])).

fof(f193,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_13 ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_13 ),
    inference(resolution,[],[f187,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f187,plain,
    ( ~ v4_lattices(sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f191,plain,
    ( ~ spl6_4
    | spl6_12 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl6_4
    | spl6_12 ),
    inference(subsumption_resolution,[],[f189,f93])).

fof(f189,plain,
    ( ~ l3_lattices(sK0)
    | spl6_12 ),
    inference(resolution,[],[f183,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f183,plain,
    ( ~ l2_lattices(sK0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_12
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f188,plain,
    ( spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_1 ),
    inference(avatar_split_clause,[],[f100,f76,f185,f181,f178])).

fof(f100,plain,
    ( ! [X12,X11] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11) )
    | spl6_1 ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f171,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10 ),
    inference(subsumption_resolution,[],[f169,f93])).

fof(f169,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_10 ),
    inference(subsumption_resolution,[],[f168,f83])).

fof(f168,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_10 ),
    inference(subsumption_resolution,[],[f167,f78])).

fof(f167,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_10 ),
    inference(resolution,[],[f155,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f155,plain,
    ( ~ v6_lattices(sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f166,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f164,f93])).

fof(f164,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_9 ),
    inference(subsumption_resolution,[],[f163,f83])).

fof(f163,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_9 ),
    inference(subsumption_resolution,[],[f162,f78])).

fof(f162,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_9 ),
    inference(resolution,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,
    ( ~ v8_lattices(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f161,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_8 ),
    inference(subsumption_resolution,[],[f159,f93])).

fof(f159,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_8 ),
    inference(subsumption_resolution,[],[f158,f83])).

fof(f158,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_8 ),
    inference(subsumption_resolution,[],[f157,f78])).

fof(f157,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_8 ),
    inference(resolution,[],[f147,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f147,plain,
    ( ~ v9_lattices(sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f156,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f140,f91,f76,f153,f149,f145,f142])).

fof(f140,plain,
    ( ! [X17] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | r3_lattices(sK0,X17,X17) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f103,f93])).

fof(f103,plain,
    ( ! [X17] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | r3_lattices(sK0,X17,X17) )
    | spl6_1 ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1) ) ),
    inference(condensation,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f128,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f38,f125])).

fof(f38,plain,(
    ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_lattice3)).

fof(f122,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f119])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:52 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.22/0.46  % (15233)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (15238)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (15243)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (15244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (15245)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (15237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (15234)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (15230)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (15236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15231)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (15250)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (15231)Refutation not found, incomplete strategy% (15231)------------------------------
% 0.22/0.50  % (15231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15231)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15231)Memory used [KB]: 10618
% 0.22/0.50  % (15231)Time elapsed: 0.092 s
% 0.22/0.50  % (15231)------------------------------
% 0.22/0.50  % (15231)------------------------------
% 0.22/0.51  % (15232)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (15251)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (15248)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (15246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (15247)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (15251)Refutation not found, incomplete strategy% (15251)------------------------------
% 0.22/0.51  % (15251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15240)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (15249)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (15242)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (15241)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (15239)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (15242)Refutation not found, incomplete strategy% (15242)------------------------------
% 0.22/0.53  % (15242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15251)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15251)Memory used [KB]: 10618
% 0.22/0.53  % (15251)Time elapsed: 0.100 s
% 0.22/0.53  % (15251)------------------------------
% 0.22/0.53  % (15251)------------------------------
% 0.22/0.53  % (15242)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15242)Memory used [KB]: 10746
% 0.22/0.53  % (15242)Time elapsed: 0.122 s
% 0.22/0.53  % (15242)------------------------------
% 0.22/0.53  % (15242)------------------------------
% 1.60/0.57  % (15233)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f1737,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f122,f128,f156,f161,f166,f171,f188,f191,f196,f265,f270,f293,f304,f318,f469,f595,f907,f925,f1122,f1196,f1203,f1468,f1473,f1698,f1728,f1736])).
% 1.60/0.57  fof(f1736,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_37 | spl6_41),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f1735])).
% 1.60/0.57  fof(f1735,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_37 | spl6_41)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1734,f1466])).
% 1.60/0.57  fof(f1466,plain,(
% 1.60/0.57    r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | ~spl6_37),
% 1.60/0.57    inference(avatar_component_clause,[],[f1465])).
% 1.60/0.57  fof(f1465,plain,(
% 1.60/0.57    spl6_37 <=> r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.60/0.57  fof(f1734,plain,(
% 1.60/0.57    ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_41)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1733,f121])).
% 1.60/0.57  fof(f121,plain,(
% 1.60/0.57    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f119])).
% 1.60/0.57  fof(f119,plain,(
% 1.60/0.57    spl6_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.60/0.57  fof(f1733,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_41)),
% 1.60/0.57    inference(resolution,[],[f1727,f211])).
% 1.60/0.57  fof(f211,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (r2_hidden(sK5(X4,sK0,X3,X5),X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f113,f93])).
% 1.60/0.57  fof(f93,plain,(
% 1.60/0.57    l3_lattices(sK0) | ~spl6_4),
% 1.60/0.57    inference(avatar_component_clause,[],[f91])).
% 1.60/0.57  fof(f91,plain,(
% 1.60/0.57    spl6_4 <=> l3_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.60/0.57  fof(f113,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(sK5(X4,sK0,X3,X5),X5) | ~r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.60/0.57    inference(subsumption_resolution,[],[f112,f78])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    ~v2_struct_0(sK0) | spl6_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f76])).
% 1.60/0.57  fof(f76,plain,(
% 1.60/0.57    spl6_1 <=> v2_struct_0(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.60/0.57  fof(f112,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(sK5(X4,sK0,X3,X5),X5) | ~r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5))) ) | (~spl6_2 | ~spl6_3)),
% 1.60/0.57    inference(subsumption_resolution,[],[f107,f83])).
% 1.60/0.57  fof(f83,plain,(
% 1.60/0.57    v10_lattices(sK0) | ~spl6_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f81])).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    spl6_2 <=> v10_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.60/0.57  fof(f107,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(sK5(X4,sK0,X3,X5),X5) | ~r2_hidden(X4,a_3_4_lattice3(sK0,X3,X5))) ) | ~spl6_3),
% 1.60/0.57    inference(resolution,[],[f88,f69])).
% 1.60/0.57  fof(f69,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | r2_hidden(sK5(X0,X1,X2,X3),X3) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f36])).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.60/0.57    inference(flattening,[],[f35])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.60/0.57    inference(ennf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,axiom,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_4_lattice3)).
% 1.60/0.57  fof(f88,plain,(
% 1.60/0.57    v4_lattice3(sK0) | ~spl6_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f86])).
% 1.60/0.57  fof(f86,plain,(
% 1.60/0.57    spl6_3 <=> v4_lattice3(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.60/0.57  fof(f1727,plain,(
% 1.60/0.57    ~r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2) | spl6_41),
% 1.60/0.57    inference(avatar_component_clause,[],[f1725])).
% 1.60/0.57  fof(f1725,plain,(
% 1.60/0.57    spl6_41 <=> r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.60/0.57  fof(f1728,plain,(
% 1.60/0.57    ~spl6_41 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_35 | spl6_40),
% 1.60/0.57    inference(avatar_split_clause,[],[f1719,f1695,f1447,f153,f149,f145,f91,f86,f81,f76,f1725])).
% 1.60/0.57  fof(f145,plain,(
% 1.60/0.57    spl6_8 <=> v9_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.60/0.57  fof(f149,plain,(
% 1.60/0.57    spl6_9 <=> v8_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.60/0.57  fof(f153,plain,(
% 1.60/0.57    spl6_10 <=> v6_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.60/0.57  fof(f1447,plain,(
% 1.60/0.57    spl6_35 <=> m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.60/0.57  fof(f1695,plain,(
% 1.60/0.57    spl6_40 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.60/0.57  fof(f1719,plain,(
% 1.60/0.57    ~r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_35 | spl6_40)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1716,f1448])).
% 1.60/0.57  fof(f1448,plain,(
% 1.60/0.57    m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl6_35),
% 1.60/0.57    inference(avatar_component_clause,[],[f1447])).
% 1.60/0.57  fof(f1716,plain,(
% 1.60/0.57    ~m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),sK2) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_40)),
% 1.60/0.57    inference(resolution,[],[f1697,f218])).
% 1.60/0.57  fof(f218,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f217,f123])).
% 1.60/0.57  fof(f123,plain,(
% 1.60/0.57    ( ! [X10] : (m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f99,f93])).
% 1.60/0.57  fof(f99,plain,(
% 1.60/0.57    ( ! [X10] : (~l3_lattices(sK0) | m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f62])).
% 1.60/0.57  fof(f62,plain,(
% 1.60/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 1.60/0.57  fof(f217,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~r2_hidden(X0,X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f216])).
% 1.60/0.57  fof(f216,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(resolution,[],[f215,f176])).
% 1.60/0.57  fof(f176,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f175,f123])).
% 1.60/0.57  fof(f175,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r1_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(resolution,[],[f174,f138])).
% 1.60/0.57  fof(f138,plain,(
% 1.60/0.57    ( ! [X2] : (r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f137,f78])).
% 1.60/0.57  fof(f137,plain,(
% 1.60/0.57    ( ! [X2] : (v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f136,f93])).
% 1.60/0.57  fof(f136,plain,(
% 1.60/0.57    ( ! [X2] : (~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f135,f88])).
% 1.60/0.57  fof(f135,plain,(
% 1.60/0.57    ( ! [X2] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f130,f83])).
% 1.60/0.57  fof(f130,plain,(
% 1.60/0.57    ( ! [X2] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X2),X2)) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(resolution,[],[f123,f71])).
% 1.60/0.57  fof(f71,plain,(
% 1.60/0.57    ( ! [X2,X0] : (~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | r3_lattice3(X0,k16_lattice3(X0,X2),X2)) )),
% 1.60/0.57    inference(equality_resolution,[],[f56])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f22])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f21])).
% 1.60/0.57  fof(f21,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 1.60/0.57  fof(f174,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (~r3_lattice3(sK0,X3,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,X5) | r1_lattices(sK0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f96,f93])).
% 1.60/0.57  fof(f96,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,X5) | r1_lattices(sK0,X3,X4) | ~r3_lattice3(sK0,X3,X5)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f58])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 1.60/0.57  fof(f215,plain,(
% 1.60/0.57    ( ! [X14,X13] : (~r1_lattices(sK0,X13,X14) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r3_lattices(sK0,X13,X14)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f214,f93])).
% 1.60/0.57  fof(f214,plain,(
% 1.60/0.57    ( ! [X14,X13] : (~l3_lattices(sK0) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_lattices(sK0,X13,X14) | r3_lattices(sK0,X13,X14)) ) | (spl6_1 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f213,f146])).
% 1.60/0.57  fof(f146,plain,(
% 1.60/0.57    v9_lattices(sK0) | ~spl6_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f145])).
% 1.60/0.57  fof(f213,plain,(
% 1.60/0.57    ( ! [X14,X13] : (~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_lattices(sK0,X13,X14) | r3_lattices(sK0,X13,X14)) ) | (spl6_1 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f212,f150])).
% 1.60/0.57  fof(f150,plain,(
% 1.60/0.57    v8_lattices(sK0) | ~spl6_9),
% 1.60/0.57    inference(avatar_component_clause,[],[f149])).
% 1.60/0.57  fof(f212,plain,(
% 1.60/0.57    ( ! [X14,X13] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_lattices(sK0,X13,X14) | r3_lattices(sK0,X13,X14)) ) | (spl6_1 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f101,f154])).
% 1.60/0.57  fof(f154,plain,(
% 1.60/0.57    v6_lattices(sK0) | ~spl6_10),
% 1.60/0.57    inference(avatar_component_clause,[],[f153])).
% 1.60/0.57  fof(f101,plain,(
% 1.60/0.57    ( ! [X14,X13] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~m1_subset_1(X14,u1_struct_0(sK0)) | ~r1_lattices(sK0,X13,X14) | r3_lattices(sK0,X13,X14)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f65])).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f34])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f33])).
% 1.60/0.57  fof(f33,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.60/0.57  fof(f1697,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | spl6_40),
% 1.60/0.57    inference(avatar_component_clause,[],[f1695])).
% 1.60/0.57  fof(f1698,plain,(
% 1.60/0.57    ~spl6_40 | spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_19 | ~spl6_24 | ~spl6_35),
% 1.60/0.57    inference(avatar_split_clause,[],[f1691,f1447,f592,f315,f153,f149,f145,f119,f91,f81,f76,f1695])).
% 1.60/0.57  fof(f315,plain,(
% 1.60/0.57    spl6_19 <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.60/0.57  fof(f592,plain,(
% 1.60/0.57    spl6_24 <=> sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.60/0.57  fof(f1691,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_19 | ~spl6_24 | ~spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1690,f317])).
% 1.60/0.57  fof(f317,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_19),
% 1.60/0.57    inference(avatar_component_clause,[],[f315])).
% 1.60/0.57  fof(f1690,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1689,f123])).
% 1.60/0.57  fof(f1689,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_35)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f1687])).
% 1.60/0.57  fof(f1687,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_24 | ~spl6_35)),
% 1.60/0.57    inference(resolution,[],[f1686,f308])).
% 1.60/0.57  fof(f308,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f307,f78])).
% 1.60/0.57  fof(f307,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f306,f93])).
% 1.60/0.57  fof(f306,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f305])).
% 1.60/0.57  fof(f305,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r3_lattice3(sK0,X0,X1)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(resolution,[],[f226,f59])).
% 1.60/0.57  fof(f59,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r3_lattice3(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f226,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f223])).
% 1.60/0.57  fof(f223,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(resolution,[],[f222,f172])).
% 1.60/0.57  fof(f172,plain,(
% 1.60/0.57    ( ! [X8,X9] : (~r1_lattices(sK0,X8,sK4(sK0,X8,X9)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r3_lattice3(sK0,X8,X9)) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f98,f93])).
% 1.60/0.57  fof(f98,plain,(
% 1.60/0.57    ( ! [X8,X9] : (~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r1_lattices(sK0,X8,sK4(sK0,X8,X9)) | r3_lattice3(sK0,X8,X9)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f61])).
% 1.60/0.57  fof(f61,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,X1,sK4(X0,X1,X2)) | r3_lattice3(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f222,plain,(
% 1.60/0.57    ( ! [X15,X16] : (r1_lattices(sK0,X15,X16) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~r3_lattices(sK0,X15,X16)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f221,f93])).
% 1.60/0.57  fof(f221,plain,(
% 1.60/0.57    ( ! [X15,X16] : (~l3_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | r1_lattices(sK0,X15,X16) | ~r3_lattices(sK0,X15,X16)) ) | (spl6_1 | ~spl6_8 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f220,f146])).
% 1.60/0.57  fof(f220,plain,(
% 1.60/0.57    ( ! [X15,X16] : (~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | r1_lattices(sK0,X15,X16) | ~r3_lattices(sK0,X15,X16)) ) | (spl6_1 | ~spl6_9 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f219,f150])).
% 1.60/0.57  fof(f219,plain,(
% 1.60/0.57    ( ! [X15,X16] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | r1_lattices(sK0,X15,X16) | ~r3_lattices(sK0,X15,X16)) ) | (spl6_1 | ~spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f102,f154])).
% 1.60/0.57  fof(f102,plain,(
% 1.60/0.57    ( ! [X15,X16] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0)) | r1_lattices(sK0,X15,X16) | ~r3_lattices(sK0,X15,X16)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f66])).
% 1.60/0.57  fof(f66,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f34])).
% 1.60/0.57  fof(f1686,plain,(
% 1.60/0.57    ( ! [X1] : (r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))) | ~r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_24 | ~spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f823,f1448])).
% 1.60/0.57  fof(f823,plain,(
% 1.60/0.57    ( ! [X1] : (r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_24)),
% 1.60/0.57    inference(subsumption_resolution,[],[f815,f121])).
% 1.60/0.57  fof(f815,plain,(
% 1.60/0.57    ( ! [X1] : (r3_lattices(sK0,X1,sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_24)),
% 1.60/0.57    inference(superposition,[],[f241,f594])).
% 1.60/0.57  fof(f594,plain,(
% 1.60/0.57    sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~spl6_24),
% 1.60/0.57    inference(avatar_component_clause,[],[f592])).
% 1.60/0.57  fof(f241,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f105,f93])).
% 1.60/0.57  fof(f105,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1))) ) | (spl6_1 | ~spl6_2)),
% 1.60/0.57    inference(subsumption_resolution,[],[f104,f78])).
% 1.60/0.57  fof(f104,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r3_lattices(sK0,X0,k3_lattices(sK0,X2,X1))) ) | ~spl6_2),
% 1.60/0.57    inference(resolution,[],[f83,f57])).
% 1.60/0.57  fof(f57,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattices(X0,X1,X2) | r3_lattices(X0,X1,k3_lattices(X0,X3,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f23])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,X1,k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f6])).
% 1.60/0.57  fof(f6,axiom,(
% 1.60/0.57    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,X1,k3_lattices(X0,X3,X2)))))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_filter_0)).
% 1.60/0.57  fof(f1473,plain,(
% 1.60/0.57    spl6_1 | ~spl6_4 | spl6_19 | spl6_37),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f1472])).
% 1.60/0.57  fof(f1472,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_4 | spl6_19 | spl6_37)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1471,f317])).
% 1.60/0.57  fof(f1471,plain,(
% 1.60/0.57    r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | spl6_37)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1470,f123])).
% 1.60/0.57  fof(f1470,plain,(
% 1.60/0.57    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | spl6_37)),
% 1.60/0.57    inference(resolution,[],[f1467,f139])).
% 1.60/0.57  fof(f139,plain,(
% 1.60/0.57    ( ! [X6,X7] : (r2_hidden(sK4(sK0,X6,X7),X7) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r3_lattice3(sK0,X6,X7)) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f97,f93])).
% 1.60/0.57  fof(f97,plain,(
% 1.60/0.57    ( ! [X6,X7] : (~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(sK4(sK0,X6,X7),X7) | r3_lattice3(sK0,X6,X7)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f1467,plain,(
% 1.60/0.57    ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_37),
% 1.60/0.57    inference(avatar_component_clause,[],[f1465])).
% 1.60/0.57  fof(f1468,plain,(
% 1.60/0.57    ~spl6_37 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_35),
% 1.60/0.57    inference(avatar_split_clause,[],[f1459,f1447,f119,f91,f86,f81,f76,f1465])).
% 1.60/0.57  fof(f1459,plain,(
% 1.60/0.57    ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1458,f78])).
% 1.60/0.57  fof(f1458,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1457,f121])).
% 1.60/0.57  fof(f1457,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1456,f93])).
% 1.60/0.57  fof(f1456,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1455,f88])).
% 1.60/0.57  fof(f1455,plain,(
% 1.60/0.57    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | spl6_35)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1454,f83])).
% 1.60/0.57  fof(f1454,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_35),
% 1.60/0.57    inference(resolution,[],[f1449,f67])).
% 1.60/0.57  fof(f67,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f36])).
% 1.60/0.57  fof(f1449,plain,(
% 1.60/0.57    ~m1_subset_1(sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | spl6_35),
% 1.60/0.57    inference(avatar_component_clause,[],[f1447])).
% 1.60/0.57  fof(f1203,plain,(
% 1.60/0.57    ~spl6_5 | ~spl6_7 | spl6_34),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f1202])).
% 1.60/0.57  fof(f1202,plain,(
% 1.60/0.57    $false | (~spl6_5 | ~spl6_7 | spl6_34)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1197,f121])).
% 1.60/0.57  fof(f1197,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_7 | spl6_34)),
% 1.60/0.57    inference(resolution,[],[f1195,f143])).
% 1.60/0.57  fof(f143,plain,(
% 1.60/0.57    ( ! [X17] : (r3_lattices(sK0,X17,X17) | ~m1_subset_1(X17,u1_struct_0(sK0))) ) | ~spl6_7),
% 1.60/0.57    inference(avatar_component_clause,[],[f142])).
% 1.60/0.57  fof(f142,plain,(
% 1.60/0.57    spl6_7 <=> ! [X17] : (~m1_subset_1(X17,u1_struct_0(sK0)) | r3_lattices(sK0,X17,X17))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.60/0.57  fof(f1195,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,sK1) | spl6_34),
% 1.60/0.57    inference(avatar_component_clause,[],[f1193])).
% 1.60/0.57  fof(f1193,plain,(
% 1.60/0.57    spl6_34 <=> r3_lattices(sK0,sK1,sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.60/0.57  fof(f1196,plain,(
% 1.60/0.57    ~spl6_34 | spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_18 | ~spl6_29),
% 1.60/0.57    inference(avatar_split_clause,[],[f1189,f905,f301,f153,f149,f145,f119,f91,f76,f1193])).
% 1.60/0.57  fof(f301,plain,(
% 1.60/0.57    spl6_18 <=> r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.60/0.57  fof(f905,plain,(
% 1.60/0.57    spl6_29 <=> ! [X4] : (r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattices(sK0,X4,sK1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.60/0.57  fof(f1189,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,sK1) | (spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_18 | ~spl6_29)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1188,f303])).
% 1.60/0.57  fof(f303,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | spl6_18),
% 1.60/0.57    inference(avatar_component_clause,[],[f301])).
% 1.60/0.57  fof(f1188,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,sK1) | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_29)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1187,f121])).
% 1.60/0.57  fof(f1187,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK1,sK1) | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_29)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f1185])).
% 1.60/0.57  fof(f1185,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_29)),
% 1.60/0.57    inference(resolution,[],[f906,f308])).
% 1.60/0.57  fof(f906,plain,(
% 1.60/0.57    ( ! [X4] : (r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattices(sK0,X4,sK1)) ) | ~spl6_29),
% 1.60/0.57    inference(avatar_component_clause,[],[f905])).
% 1.60/0.57  fof(f1122,plain,(
% 1.60/0.57    spl6_1 | ~spl6_4 | ~spl6_5 | spl6_18 | spl6_30),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f1121])).
% 1.60/0.57  fof(f1121,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_4 | ~spl6_5 | spl6_18 | spl6_30)),
% 1.60/0.57    inference(subsumption_resolution,[],[f1099,f303])).
% 1.60/0.57  fof(f1099,plain,(
% 1.60/0.57    r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | ~spl6_5 | spl6_30)),
% 1.60/0.57    inference(subsumption_resolution,[],[f941,f121])).
% 1.60/0.57  fof(f941,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_4 | spl6_30)),
% 1.60/0.57    inference(resolution,[],[f924,f139])).
% 1.60/0.57  fof(f924,plain,(
% 1.60/0.57    ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_30),
% 1.60/0.57    inference(avatar_component_clause,[],[f922])).
% 1.60/0.57  fof(f922,plain,(
% 1.60/0.57    spl6_30 <=> r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.60/0.57  fof(f925,plain,(
% 1.60/0.57    ~spl6_30 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_28),
% 1.60/0.57    inference(avatar_split_clause,[],[f913,f901,f119,f91,f86,f81,f76,f922])).
% 1.60/0.57  fof(f901,plain,(
% 1.60/0.57    spl6_28 <=> m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.60/0.57  fof(f913,plain,(
% 1.60/0.57    ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f912,f78])).
% 1.60/0.57  fof(f912,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f911,f121])).
% 1.60/0.57  fof(f911,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f910,f93])).
% 1.60/0.57  fof(f910,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | ~spl6_3 | spl6_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f909,f88])).
% 1.60/0.57  fof(f909,plain,(
% 1.60/0.57    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | (~spl6_2 | spl6_28)),
% 1.60/0.57    inference(subsumption_resolution,[],[f908,f83])).
% 1.60/0.57  fof(f908,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_28),
% 1.60/0.57    inference(resolution,[],[f903,f67])).
% 1.60/0.57  fof(f903,plain,(
% 1.60/0.57    ~m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | spl6_28),
% 1.60/0.57    inference(avatar_component_clause,[],[f901])).
% 1.60/0.57  fof(f907,plain,(
% 1.60/0.57    ~spl6_28 | spl6_29 | spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_23),
% 1.60/0.57    inference(avatar_split_clause,[],[f623,f466,f178,f119,f91,f81,f76,f905,f901])).
% 1.60/0.57  fof(f178,plain,(
% 1.60/0.57    spl6_11 <=> ! [X11,X12] : (~m1_subset_1(X11,u1_struct_0(sK0)) | k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11) | ~m1_subset_1(X12,u1_struct_0(sK0)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.60/0.57  fof(f466,plain,(
% 1.60/0.57    spl6_23 <=> sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.60/0.57  fof(f623,plain,(
% 1.60/0.57    ( ! [X4] : (r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_23)),
% 1.60/0.57    inference(subsumption_resolution,[],[f615,f121])).
% 1.60/0.57  fof(f615,plain,(
% 1.60/0.57    ( ! [X4] : (r3_lattices(sK0,X4,sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_11 | ~spl6_23)),
% 1.60/0.57    inference(superposition,[],[f251,f468])).
% 1.60/0.57  fof(f468,plain,(
% 1.60/0.57    sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | ~spl6_23),
% 1.60/0.57    inference(avatar_component_clause,[],[f466])).
% 1.60/0.57  fof(f251,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (r3_lattices(sK0,X5,k3_lattices(sK0,X4,X3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X5,X4) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_11)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f250])).
% 1.60/0.57  fof(f250,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (r3_lattices(sK0,X5,k3_lattices(sK0,X4,X3)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X5,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_11)),
% 1.60/0.57    inference(superposition,[],[f241,f179])).
% 1.60/0.57  fof(f179,plain,(
% 1.60/0.57    ( ! [X12,X11] : (k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0))) ) | ~spl6_11),
% 1.60/0.57    inference(avatar_component_clause,[],[f178])).
% 1.60/0.57  fof(f595,plain,(
% 1.60/0.57    spl6_24 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19),
% 1.60/0.57    inference(avatar_split_clause,[],[f352,f315,f119,f91,f86,f81,f76,f592])).
% 1.60/0.57  fof(f352,plain,(
% 1.60/0.57    sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19)),
% 1.60/0.57    inference(subsumption_resolution,[],[f351,f123])).
% 1.60/0.57  fof(f351,plain,(
% 1.60/0.57    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_19)),
% 1.60/0.57    inference(subsumption_resolution,[],[f347,f121])).
% 1.60/0.57  fof(f347,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_19)),
% 1.60/0.57    inference(resolution,[],[f229,f317])).
% 1.60/0.57  fof(f229,plain,(
% 1.60/0.57    ( ! [X4,X5,X3] : (r3_lattice3(sK0,X4,a_3_4_lattice3(sK0,X3,X5)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | sK4(sK0,X4,a_3_4_lattice3(sK0,X3,X5)) = k3_lattices(sK0,X3,sK5(sK4(sK0,X4,a_3_4_lattice3(sK0,X3,X5)),sK0,X3,X5))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(resolution,[],[f227,f139])).
% 1.60/0.57  fof(f227,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f111,f93])).
% 1.60/0.57  fof(f111,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1 | ~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.60/0.57    inference(subsumption_resolution,[],[f110,f78])).
% 1.60/0.57  fof(f110,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1 | ~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))) ) | (~spl6_2 | ~spl6_3)),
% 1.60/0.57    inference(subsumption_resolution,[],[f106,f83])).
% 1.60/0.57  fof(f106,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,sK5(X1,sK0,X0,X2)) = X1 | ~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))) ) | ~spl6_3),
% 1.60/0.57    inference(resolution,[],[f88,f68])).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0 | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f36])).
% 1.60/0.57  fof(f469,plain,(
% 1.60/0.57    spl6_23 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_18),
% 1.60/0.57    inference(avatar_split_clause,[],[f350,f301,f119,f91,f86,f81,f76,f466])).
% 1.60/0.57  fof(f350,plain,(
% 1.60/0.57    sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_18)),
% 1.60/0.57    inference(subsumption_resolution,[],[f348,f121])).
% 1.60/0.57  fof(f348,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_18)),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f346])).
% 1.60/0.57  fof(f346,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) = k3_lattices(sK0,sK1,sK5(sK4(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)),sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_18)),
% 1.60/0.57    inference(resolution,[],[f229,f303])).
% 1.60/0.57  fof(f318,plain,(
% 1.60/0.57    ~spl6_19 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_16),
% 1.60/0.57    inference(avatar_split_clause,[],[f299,f286,f91,f86,f81,f76,f315])).
% 1.60/0.57  fof(f286,plain,(
% 1.60/0.57    spl6_16 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.60/0.57  fof(f299,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_16)),
% 1.60/0.57    inference(subsumption_resolution,[],[f297,f123])).
% 1.60/0.57  fof(f297,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),a_3_4_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_16)),
% 1.60/0.57    inference(resolution,[],[f288,f134])).
% 1.60/0.57  fof(f134,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f133,f78])).
% 1.60/0.57  fof(f133,plain,(
% 1.60/0.57    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f132,f93])).
% 1.60/0.57  fof(f132,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f131,f88])).
% 1.60/0.57  fof(f131,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl6_1 | ~spl6_2 | ~spl6_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f129,f83])).
% 1.60/0.57  fof(f129,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.57    inference(resolution,[],[f123,f72])).
% 1.60/0.57  fof(f72,plain,(
% 1.60/0.57    ( ! [X2,X0,X3] : (~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 1.60/0.57    inference(equality_resolution,[],[f55])).
% 1.60/0.57  fof(f55,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f22])).
% 1.60/0.57  fof(f288,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | spl6_16),
% 1.60/0.57    inference(avatar_component_clause,[],[f286])).
% 1.60/0.57  fof(f304,plain,(
% 1.60/0.57    ~spl6_18 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_17),
% 1.60/0.57    inference(avatar_split_clause,[],[f295,f290,f119,f91,f86,f81,f76,f301])).
% 1.60/0.57  fof(f290,plain,(
% 1.60/0.57    spl6_17 <=> r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.60/0.57  fof(f295,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_17)),
% 1.60/0.57    inference(subsumption_resolution,[],[f294,f121])).
% 1.60/0.57  fof(f294,plain,(
% 1.60/0.57    ~r3_lattice3(sK0,sK1,a_3_4_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_17)),
% 1.60/0.57    inference(resolution,[],[f292,f134])).
% 1.60/0.57  fof(f292,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | spl6_17),
% 1.60/0.57    inference(avatar_component_clause,[],[f290])).
% 1.60/0.57  fof(f293,plain,(
% 1.60/0.57    ~spl6_16 | ~spl6_17 | spl6_1 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_14),
% 1.60/0.57    inference(avatar_split_clause,[],[f284,f259,f125,f119,f91,f76,f290,f286])).
% 1.60/0.57  fof(f125,plain,(
% 1.60/0.57    spl6_6 <=> r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.60/0.57  fof(f259,plain,(
% 1.60/0.57    spl6_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) | ~r3_lattices(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.60/0.57  fof(f284,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | (spl6_1 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_14)),
% 1.60/0.57    inference(subsumption_resolution,[],[f283,f123])).
% 1.60/0.57  fof(f283,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | (spl6_1 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_14)),
% 1.60/0.57    inference(subsumption_resolution,[],[f282,f123])).
% 1.60/0.57  fof(f282,plain,(
% 1.60/0.57    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | (~spl6_5 | spl6_6 | ~spl6_14)),
% 1.60/0.57    inference(subsumption_resolution,[],[f277,f121])).
% 1.60/0.57  fof(f277,plain,(
% 1.60/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK1,k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | ~m1_subset_1(k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | (spl6_6 | ~spl6_14)),
% 1.60/0.57    inference(resolution,[],[f260,f127])).
% 1.60/0.57  fof(f127,plain,(
% 1.60/0.57    ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | spl6_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f125])).
% 1.60/0.57  fof(f260,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X2)) ) | ~spl6_14),
% 1.60/0.57    inference(avatar_component_clause,[],[f259])).
% 1.60/0.57  fof(f270,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_4 | spl6_15),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f269])).
% 1.60/0.57  fof(f269,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | spl6_15)),
% 1.60/0.57    inference(subsumption_resolution,[],[f268,f93])).
% 1.60/0.57  fof(f268,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | (spl6_1 | ~spl6_2 | spl6_15)),
% 1.60/0.57    inference(subsumption_resolution,[],[f267,f83])).
% 1.60/0.57  fof(f267,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl6_1 | spl6_15)),
% 1.60/0.57    inference(subsumption_resolution,[],[f266,f78])).
% 1.60/0.57  fof(f266,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl6_15),
% 1.60/0.57    inference(resolution,[],[f264,f46])).
% 1.60/0.57  fof(f46,plain,(
% 1.60/0.57    ( ! [X0] : (v5_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f18,plain,(
% 1.60/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.60/0.57    inference(flattening,[],[f17])).
% 1.60/0.57  fof(f17,plain,(
% 1.60/0.57    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.60/0.57  fof(f264,plain,(
% 1.60/0.57    ~v5_lattices(sK0) | spl6_15),
% 1.60/0.57    inference(avatar_component_clause,[],[f262])).
% 1.60/0.57  fof(f262,plain,(
% 1.60/0.57    spl6_15 <=> v5_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.60/0.57  fof(f265,plain,(
% 1.60/0.57    spl6_14 | ~spl6_15 | spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_13),
% 1.60/0.57    inference(avatar_split_clause,[],[f257,f185,f153,f149,f145,f91,f76,f262,f259])).
% 1.60/0.57  fof(f185,plain,(
% 1.60/0.57    spl6_13 <=> v4_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.60/0.57  fof(f257,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v5_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | (spl6_1 | ~spl6_4 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f256,f93])).
% 1.60/0.57  fof(f256,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v5_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | (spl6_1 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f255,f146])).
% 1.60/0.57  fof(f255,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v5_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | (spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f254,f150])).
% 1.60/0.57  fof(f254,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v5_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | (spl6_1 | ~spl6_10 | ~spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f253,f154])).
% 1.60/0.57  fof(f253,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v5_lattices(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | (spl6_1 | ~spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f95,f186])).
% 1.60/0.57  fof(f186,plain,(
% 1.60/0.57    v4_lattices(sK0) | ~spl6_13),
% 1.60/0.57    inference(avatar_component_clause,[],[f185])).
% 1.60/0.57  fof(f95,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~v4_lattices(sK0) | ~v5_lattices(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X2) | ~r3_lattices(sK0,X1,X2) | r3_lattices(sK0,k3_lattices(sK0,X0,X1),X2)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f51])).
% 1.60/0.57  fof(f51,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~v5_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattices(X0,X1,X3) | ~r3_lattices(X0,X2,X3) | r3_lattices(X0,k3_lattices(X0,X1,X2),X3)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f20])).
% 1.60/0.57  fof(f20,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,k3_lattices(X0,X1,X2),X3) | ~r3_lattices(X0,X2,X3) | ~r3_lattices(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f19])).
% 1.60/0.57  fof(f19,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,k3_lattices(X0,X1,X2),X3) | (~r3_lattices(X0,X2,X3) | ~r3_lattices(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_lattices(X0,X2,X3) & r3_lattices(X0,X1,X3)) => r3_lattices(X0,k3_lattices(X0,X1,X2),X3))))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_0)).
% 1.60/0.57  fof(f196,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_4 | spl6_13),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 1.60/0.57  fof(f195,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f194,f93])).
% 1.60/0.57  fof(f194,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | (spl6_1 | ~spl6_2 | spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f193,f83])).
% 1.60/0.57  fof(f193,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl6_1 | spl6_13)),
% 1.60/0.57    inference(subsumption_resolution,[],[f192,f78])).
% 1.60/0.57  fof(f192,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl6_13),
% 1.60/0.57    inference(resolution,[],[f187,f45])).
% 1.60/0.57  fof(f45,plain,(
% 1.60/0.57    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f187,plain,(
% 1.60/0.57    ~v4_lattices(sK0) | spl6_13),
% 1.60/0.57    inference(avatar_component_clause,[],[f185])).
% 1.60/0.57  fof(f191,plain,(
% 1.60/0.57    ~spl6_4 | spl6_12),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f190])).
% 1.60/0.57  fof(f190,plain,(
% 1.60/0.57    $false | (~spl6_4 | spl6_12)),
% 1.60/0.57    inference(subsumption_resolution,[],[f189,f93])).
% 1.60/0.57  fof(f189,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | spl6_12),
% 1.60/0.57    inference(resolution,[],[f183,f44])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f16])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.60/0.57  fof(f183,plain,(
% 1.60/0.57    ~l2_lattices(sK0) | spl6_12),
% 1.60/0.57    inference(avatar_component_clause,[],[f181])).
% 1.60/0.57  fof(f181,plain,(
% 1.60/0.57    spl6_12 <=> l2_lattices(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.60/0.57  fof(f188,plain,(
% 1.60/0.57    spl6_11 | ~spl6_12 | ~spl6_13 | spl6_1),
% 1.60/0.57    inference(avatar_split_clause,[],[f100,f76,f185,f181,f178])).
% 1.60/0.57  fof(f100,plain,(
% 1.60/0.57    ( ! [X12,X11] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | k3_lattices(sK0,X11,X12) = k3_lattices(sK0,X12,X11)) ) | spl6_1),
% 1.60/0.57    inference(resolution,[],[f78,f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.57    inference(flattening,[],[f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f2])).
% 1.60/0.57  fof(f2,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 1.60/0.57  fof(f171,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_4 | spl6_10),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f170])).
% 1.60/0.57  fof(f170,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f169,f93])).
% 1.60/0.57  fof(f169,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | (spl6_1 | ~spl6_2 | spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f168,f83])).
% 1.60/0.57  fof(f168,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl6_1 | spl6_10)),
% 1.60/0.57    inference(subsumption_resolution,[],[f167,f78])).
% 1.60/0.57  fof(f167,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl6_10),
% 1.60/0.57    inference(resolution,[],[f155,f47])).
% 1.60/0.57  fof(f47,plain,(
% 1.60/0.57    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f155,plain,(
% 1.60/0.57    ~v6_lattices(sK0) | spl6_10),
% 1.60/0.57    inference(avatar_component_clause,[],[f153])).
% 1.60/0.57  fof(f166,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_4 | spl6_9),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f165])).
% 1.60/0.57  fof(f165,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | spl6_9)),
% 1.60/0.57    inference(subsumption_resolution,[],[f164,f93])).
% 1.60/0.57  fof(f164,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | (spl6_1 | ~spl6_2 | spl6_9)),
% 1.60/0.57    inference(subsumption_resolution,[],[f163,f83])).
% 1.60/0.57  fof(f163,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl6_1 | spl6_9)),
% 1.60/0.57    inference(subsumption_resolution,[],[f162,f78])).
% 1.60/0.57  fof(f162,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl6_9),
% 1.60/0.57    inference(resolution,[],[f151,f49])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f151,plain,(
% 1.60/0.57    ~v8_lattices(sK0) | spl6_9),
% 1.60/0.57    inference(avatar_component_clause,[],[f149])).
% 1.60/0.57  fof(f161,plain,(
% 1.60/0.57    spl6_1 | ~spl6_2 | ~spl6_4 | spl6_8),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f160])).
% 1.60/0.57  fof(f160,plain,(
% 1.60/0.57    $false | (spl6_1 | ~spl6_2 | ~spl6_4 | spl6_8)),
% 1.60/0.57    inference(subsumption_resolution,[],[f159,f93])).
% 1.60/0.57  fof(f159,plain,(
% 1.60/0.57    ~l3_lattices(sK0) | (spl6_1 | ~spl6_2 | spl6_8)),
% 1.60/0.57    inference(subsumption_resolution,[],[f158,f83])).
% 1.60/0.57  fof(f158,plain,(
% 1.60/0.57    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl6_1 | spl6_8)),
% 1.60/0.57    inference(subsumption_resolution,[],[f157,f78])).
% 1.60/0.57  fof(f157,plain,(
% 1.60/0.57    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl6_8),
% 1.60/0.57    inference(resolution,[],[f147,f50])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f18])).
% 1.60/0.57  fof(f147,plain,(
% 1.60/0.57    ~v9_lattices(sK0) | spl6_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f145])).
% 1.60/0.57  fof(f156,plain,(
% 1.60/0.57    spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_1 | ~spl6_4),
% 1.60/0.57    inference(avatar_split_clause,[],[f140,f91,f76,f153,f149,f145,f142])).
% 1.60/0.58  fof(f140,plain,(
% 1.60/0.58    ( ! [X17] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(X17,u1_struct_0(sK0)) | r3_lattices(sK0,X17,X17)) ) | (spl6_1 | ~spl6_4)),
% 1.60/0.58    inference(subsumption_resolution,[],[f103,f93])).
% 1.60/0.58  fof(f103,plain,(
% 1.60/0.58    ( ! [X17] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X17,u1_struct_0(sK0)) | r3_lattices(sK0,X17,X17)) ) | spl6_1),
% 1.60/0.58    inference(resolution,[],[f78,f74])).
% 1.60/0.58  fof(f74,plain,(
% 1.60/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattices(X0,X1,X1)) )),
% 1.60/0.58    inference(condensation,[],[f64])).
% 1.60/0.58  fof(f64,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_lattices(X0,X1,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f32])).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f31])).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).
% 1.60/0.58  fof(f128,plain,(
% 1.60/0.58    ~spl6_6),
% 1.60/0.58    inference(avatar_split_clause,[],[f38,f125])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  fof(f15,plain,(
% 1.75/0.58    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.75/0.58    inference(flattening,[],[f14])).
% 1.75/0.58  fof(f14,plain,(
% 1.75/0.58    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f13])).
% 1.75/0.58  fof(f13,negated_conjecture,(
% 1.75/0.58    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 1.75/0.58    inference(negated_conjecture,[],[f12])).
% 1.75/0.58  fof(f12,conjecture,(
% 1.75/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_lattice3)).
% 1.75/0.58  fof(f122,plain,(
% 1.75/0.58    spl6_5),
% 1.75/0.58    inference(avatar_split_clause,[],[f37,f119])).
% 1.75/0.58  fof(f37,plain,(
% 1.75/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.75/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  fof(f94,plain,(
% 1.75/0.58    spl6_4),
% 1.75/0.58    inference(avatar_split_clause,[],[f42,f91])).
% 1.75/0.58  fof(f42,plain,(
% 1.75/0.58    l3_lattices(sK0)),
% 1.75/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  fof(f89,plain,(
% 1.75/0.58    spl6_3),
% 1.75/0.58    inference(avatar_split_clause,[],[f41,f86])).
% 1.75/0.58  fof(f41,plain,(
% 1.75/0.58    v4_lattice3(sK0)),
% 1.75/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  fof(f84,plain,(
% 1.75/0.58    spl6_2),
% 1.75/0.58    inference(avatar_split_clause,[],[f40,f81])).
% 1.75/0.58  fof(f40,plain,(
% 1.75/0.58    v10_lattices(sK0)),
% 1.75/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  fof(f79,plain,(
% 1.75/0.58    ~spl6_1),
% 1.75/0.58    inference(avatar_split_clause,[],[f39,f76])).
% 1.75/0.58  fof(f39,plain,(
% 1.75/0.58    ~v2_struct_0(sK0)),
% 1.75/0.58    inference(cnf_transformation,[],[f15])).
% 1.75/0.58  % SZS output end Proof for theBenchmark
% 1.75/0.58  % (15233)------------------------------
% 1.75/0.58  % (15233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.58  % (15233)Termination reason: Refutation
% 1.75/0.58  
% 1.75/0.58  % (15233)Memory used [KB]: 12025
% 1.75/0.58  % (15233)Time elapsed: 0.157 s
% 1.75/0.58  % (15233)------------------------------
% 1.75/0.58  % (15233)------------------------------
% 1.75/0.58  % (15226)Success in time 0.218 s
%------------------------------------------------------------------------------
