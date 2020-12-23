%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t42_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  319 ( 677 expanded)
%              Number of leaves         :   75 ( 246 expanded)
%              Depth                    :   27
%              Number of atoms          : 1251 (2603 expanded)
%              Number of equality atoms :   74 ( 150 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f120,f127,f134,f141,f148,f155,f162,f169,f176,f184,f196,f203,f229,f237,f247,f260,f267,f291,f312,f324,f331,f337,f346,f347,f355,f362,f369,f374,f381,f384,f421,f439,f488,f518,f538,f545,f570,f694,f699,f707,f712,f717,f771,f857,f912,f1012,f1038])).

fof(f1038,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1037])).

fof(f1037,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1036,f154])).

fof(f154,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1036,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1035,f140])).

fof(f140,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_8
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1035,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1034,f126])).

fof(f126,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_4
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1034,plain,
    ( ~ v4_lattice3(sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1033,f119])).

fof(f119,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1033,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1032,f161])).

fof(f161,plain,
    ( k16_lattice3(sK0,sK2) != sK1
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl7_15
  <=> k16_lattice3(sK0,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1032,plain,
    ( k16_lattice3(sK0,sK2) = sK1
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f1031,f133])).

fof(f133,plain,
    ( l3_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1031,plain,
    ( ~ l3_lattices(sK0)
    | k16_lattice3(sK0,sK2) = sK1
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f1027,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1027,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | k16_lattice3(sK0,sK2) = sK1
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f826,f147])).

fof(f147,plain,
    ( r3_lattice3(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_10
  <=> r3_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f826,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X1,X0,X2)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f819])).

fof(f819,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r3_lattice3(X1,X0,X2)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f664,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t40_lattice3)).

fof(f664,plain,(
    ! [X10,X8,X9] :
      ( ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ l3_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f663,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',dt_k16_lattice3)).

fof(f663,plain,(
    ! [X10,X8,X9] :
      ( ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | k16_lattice3(X8,X10) = X9
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f662,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',cc1_lattices)).

fof(f662,plain,(
    ! [X10,X8,X9] :
      ( ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ v4_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f661,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f661,plain,(
    ! [X10,X8,X9] :
      ( ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ v4_lattices(X8)
      | ~ v6_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f660,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f660,plain,(
    ! [X10,X8,X9] :
      ( ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ v4_lattices(X8)
      | ~ v6_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v8_lattices(X8)
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f646,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f646,plain,(
    ! [X10,X8,X9] :
      ( ~ v9_lattices(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ v4_lattices(X8)
      | ~ v6_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v8_lattices(X8)
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ r2_hidden(X9,X10) ) ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,(
    ! [X10,X8,X9] :
      ( ~ v9_lattices(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(k16_lattice3(X8,X10),u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ r3_lattices(X8,X9,k16_lattice3(X8,X10))
      | ~ v4_lattices(X8)
      | ~ v6_lattices(X8)
      | k16_lattice3(X8,X10) = X9
      | ~ v8_lattices(X8)
      | ~ v10_lattices(X8)
      | ~ v4_lattice3(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ r2_hidden(X9,X10)
      | v2_struct_0(X8) ) ),
    inference(resolution,[],[f529,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t38_lattice3)).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X2,X1)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | ~ v6_lattices(X0)
      | X1 = X2
      | ~ v8_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | ~ v6_lattices(X0)
      | X1 = X2
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X2,X1) ) ),
    inference(resolution,[],[f317,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',redefinition_r3_lattices)).

fof(f317,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattices(X3,X5,X4)
      | ~ v8_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ r3_lattices(X3,X4,X5)
      | ~ v4_lattices(X3)
      | ~ v6_lattices(X3)
      | X4 = X5 ) ),
    inference(subsumption_resolution,[],[f315,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',dt_l3_lattices)).

fof(f315,plain,(
    ! [X4,X5,X3] :
      ( ~ v6_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ r3_lattices(X3,X4,X5)
      | ~ v4_lattices(X3)
      | ~ l2_lattices(X3)
      | ~ r1_lattices(X3,X5,X4)
      | X4 = X5 ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X4,X5,X3] :
      ( ~ v6_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ r3_lattices(X3,X4,X5)
      | ~ v4_lattices(X3)
      | ~ l2_lattices(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r1_lattices(X3,X5,X4)
      | v2_struct_0(X3)
      | X4 = X5 ) ),
    inference(resolution,[],[f96,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t26_lattices)).

fof(f1012,plain,
    ( ~ spl7_97
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f972,f846,f1010])).

fof(f1010,plain,
    ( spl7_97
  <=> ~ r2_hidden(a_2_1_lattice3(sK0,sK2),sK5(a_2_1_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f846,plain,
    ( spl7_90
  <=> r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f972,plain,
    ( ~ r2_hidden(a_2_1_lattice3(sK0,sK2),sK5(a_2_1_lattice3(sK0,sK2)))
    | ~ spl7_90 ),
    inference(resolution,[],[f847,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',antisymmetry_r2_hidden)).

fof(f847,plain,
    ( r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f846])).

fof(f912,plain,
    ( spl7_94
    | spl7_91 ),
    inference(avatar_split_clause,[],[f896,f849,f910])).

fof(f910,plain,
    ( spl7_94
  <=> v1_xboole_0(a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f849,plain,
    ( spl7_91
  <=> ~ r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f896,plain,
    ( v1_xboole_0(a_2_1_lattice3(sK0,sK2))
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f895,f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',existence_m1_subset_1)).

fof(f895,plain,
    ( v1_xboole_0(a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_91 ),
    inference(resolution,[],[f850,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t2_subset)).

fof(f850,plain,
    ( ~ r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f849])).

fof(f857,plain,
    ( ~ spl7_91
    | spl7_92
    | spl7_1
    | ~ spl7_6
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f816,f769,f132,f111,f855,f849])).

fof(f855,plain,
    ( spl7_92
  <=> r3_lattice3(sK0,sK5(a_2_1_lattice3(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f769,plain,
    ( spl7_88
  <=> sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f816,plain,
    ( r3_lattice3(sK0,sK5(a_2_1_lattice3(sK0,sK2)),sK2)
    | ~ r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f815,f112])).

fof(f815,plain,
    ( r3_lattice3(sK0,sK5(a_2_1_lattice3(sK0,sK2)),sK2)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_6
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f809,f133])).

fof(f809,plain,
    ( r3_lattice3(sK0,sK5(a_2_1_lattice3(sK0,sK2)),sK2)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK5(a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ spl7_88 ),
    inference(superposition,[],[f75,f770])).

fof(f770,plain,
    ( sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f769])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK3(X0,X1,X2),X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',fraenkel_a_2_1_lattice3)).

fof(f771,plain,
    ( spl7_88
    | spl7_1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f763,f153,f146,f132,f111,f769])).

fof(f763,plain,
    ( sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f762,f112])).

fof(f762,plain,
    ( sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f761,f154])).

fof(f761,plain,
    ( sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f758,f133])).

fof(f758,plain,
    ( sK3(sK5(a_2_1_lattice3(sK0,sK2)),sK0,sK2) = sK5(a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f609,f147])).

fof(f609,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X2,X1)
      | sK3(sK5(a_2_1_lattice3(X0,X1)),X0,X1) = sK5(a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f606])).

fof(f606,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | sK3(sK5(a_2_1_lattice3(X0,X1)),X0,X1) = sK5(a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f501,f295])).

fof(f295,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_xboole_0(a_2_1_lattice3(X9,X11))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ r3_lattice3(X9,X10,X11)
      | v2_struct_0(X9)
      | ~ l3_lattices(X9) ) ),
    inference(resolution,[],[f106,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t7_boole)).

fof(f106,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattice3(X1,X3,X2)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r3_lattice3(X1,X3,X2)
      | r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f501,plain,(
    ! [X10,X9] :
      ( v1_xboole_0(a_2_1_lattice3(X9,X10))
      | v2_struct_0(X9)
      | sK3(sK5(a_2_1_lattice3(X9,X10)),X9,X10) = sK5(a_2_1_lattice3(X9,X10))
      | ~ l3_lattices(X9) ) ),
    inference(resolution,[],[f276,f94])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,a_2_1_lattice3(X0,X2))
      | sK3(X1,X0,X2) = X1
      | v2_struct_0(X0)
      | v1_xboole_0(a_2_1_lattice3(X0,X2))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f74,f89])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f717,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_87 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f715,f133])).

fof(f715,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f714,f119])).

fof(f714,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f713,f112])).

fof(f713,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_87 ),
    inference(resolution,[],[f693,f105])).

fof(f693,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl7_87 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl7_87
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f712,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_83 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f710,f133])).

fof(f710,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f709,f119])).

fof(f709,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f708,f112])).

fof(f708,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_83 ),
    inference(resolution,[],[f684,f100])).

fof(f684,plain,
    ( ~ v4_lattices(sK0)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f683])).

fof(f683,plain,
    ( spl7_83
  <=> ~ v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f707,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_81 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f705,f133])).

fof(f705,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f704,f119])).

fof(f704,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f703,f112])).

fof(f703,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_81 ),
    inference(resolution,[],[f678,f102])).

fof(f678,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl7_81
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f699,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | spl7_79 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_79 ),
    inference(subsumption_resolution,[],[f697,f133])).

fof(f697,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_79 ),
    inference(subsumption_resolution,[],[f696,f119])).

fof(f696,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_1
    | ~ spl7_79 ),
    inference(subsumption_resolution,[],[f695,f112])).

fof(f695,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl7_79 ),
    inference(resolution,[],[f672,f104])).

fof(f672,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl7_79 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl7_79
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f694,plain,
    ( ~ spl7_79
    | ~ spl7_81
    | ~ spl7_83
    | spl7_84
    | ~ spl7_87
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f666,f132,f125,f118,f111,f692,f686,f683,f677,f671])).

fof(f686,plain,
    ( spl7_84
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X11),u1_struct_0(sK0))
        | ~ r2_hidden(X12,a_2_1_lattice3(sK0,X11))
        | k16_lattice3(sK0,X11) = X12
        | ~ r3_lattices(sK0,k16_lattice3(sK0,X11),X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f666,plain,
    ( ! [X12,X11] :
        ( ~ v9_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X11),u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k16_lattice3(sK0,X11),X12)
        | ~ v4_lattices(sK0)
        | ~ v6_lattices(sK0)
        | k16_lattice3(sK0,X11) = X12
        | ~ v8_lattices(sK0)
        | ~ r2_hidden(X12,a_2_1_lattice3(sK0,X11)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f665,f112])).

fof(f665,plain,
    ( ! [X12,X11] :
        ( ~ v9_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X11),u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_lattices(sK0,k16_lattice3(sK0,X11),X12)
        | ~ v4_lattices(sK0)
        | ~ v6_lattices(sK0)
        | k16_lattice3(sK0,X11) = X12
        | ~ v8_lattices(sK0)
        | ~ r2_hidden(X12,a_2_1_lattice3(sK0,X11)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f645,f133])).

fof(f645,plain,
    ( ! [X12,X11] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X11),u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_lattices(sK0,k16_lattice3(sK0,X11),X12)
        | ~ v4_lattices(sK0)
        | ~ v6_lattices(sK0)
        | k16_lattice3(sK0,X11) = X12
        | ~ v8_lattices(sK0)
        | ~ r2_hidden(X12,a_2_1_lattice3(sK0,X11)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,
    ( ! [X12,X11] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X11),u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r3_lattices(sK0,k16_lattice3(sK0,X11),X12)
        | ~ v4_lattices(sK0)
        | ~ v6_lattices(sK0)
        | k16_lattice3(sK0,X11) = X12
        | ~ v8_lattices(sK0)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r2_hidden(X12,a_2_1_lattice3(sK0,X11)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f529,f391])).

fof(f391,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f390,f112])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f389,f133])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f388,f126])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f386,f119])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k16_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(superposition,[],[f86,f275])).

fof(f275,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0))
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f273,f112])).

fof(f273,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f133])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',d22_lattice3)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f570,plain,
    ( ~ spl7_75
    | spl7_76
    | ~ spl7_12
    | spl7_39 ),
    inference(avatar_split_clause,[],[f557,f286,f153,f568,f562])).

fof(f562,plain,
    ( spl7_75
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f568,plain,
    ( spl7_76
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f286,plain,
    ( spl7_39
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f557,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl7_12
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f549,f287])).

fof(f287,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f286])).

fof(f549,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f395,f154])).

fof(f395,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f187,f89])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f89,f91])).

fof(f545,plain,
    ( ~ spl7_73
    | spl7_66
    | spl7_51 ),
    inference(avatar_split_clause,[],[f393,f360,f486,f543])).

fof(f543,plain,
    ( spl7_73
  <=> ~ m1_subset_1(k16_lattice3(sK0,sK2),sK4(sK1,k16_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f486,plain,
    ( spl7_66
  <=> v1_xboole_0(sK4(sK1,k16_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f360,plain,
    ( spl7_51
  <=> ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(sK1,k16_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f393,plain,
    ( v1_xboole_0(sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_51 ),
    inference(resolution,[],[f361,f89])).

fof(f361,plain,
    ( ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f360])).

fof(f538,plain,
    ( ~ spl7_71
    | spl7_58
    | spl7_43 ),
    inference(avatar_split_clause,[],[f392,f322,f419,f536])).

fof(f536,plain,
    ( spl7_71
  <=> ~ m1_subset_1(k16_lattice3(sK0,sK2),sK4(k16_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f419,plain,
    ( spl7_58
  <=> v1_xboole_0(sK4(k16_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f322,plain,
    ( spl7_43
  <=> ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(k16_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f392,plain,
    ( v1_xboole_0(sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_43 ),
    inference(resolution,[],[f323,f89])).

fof(f323,plain,
    ( ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f322])).

fof(f518,plain,
    ( spl7_68
    | spl7_1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f496,f153,f146,f132,f111,f516])).

fof(f516,plain,
    ( spl7_68
  <=> sK1 = sK3(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f496,plain,
    ( sK1 = sK3(sK1,sK0,sK2)
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f495,f112])).

fof(f495,plain,
    ( v2_struct_0(sK0)
    | sK1 = sK3(sK1,sK0,sK2)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f494,f133])).

fof(f494,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = sK3(sK1,sK0,sK2)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f491,f154])).

fof(f491,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = sK3(sK1,sK0,sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f297,f147])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sK3(X1,X0,X2) = X1 ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | sK3(X1,X0,X2) = X1
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f106,f74])).

fof(f488,plain,
    ( ~ spl7_65
    | spl7_66
    | spl7_55 ),
    inference(avatar_split_clause,[],[f385,f379,f486,f480])).

fof(f480,plain,
    ( spl7_65
  <=> ~ m1_subset_1(sK1,sK4(sK1,k16_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f379,plain,
    ( spl7_55
  <=> ~ r2_hidden(sK1,sK4(sK1,k16_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f385,plain,
    ( v1_xboole_0(sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ m1_subset_1(sK1,sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_55 ),
    inference(resolution,[],[f380,f89])).

fof(f380,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f379])).

fof(f439,plain,
    ( spl7_60
    | spl7_62
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f274,f167,f437,f431])).

fof(f431,plain,
    ( spl7_60
  <=> ! [X1] : k16_lattice3(sK6,X1) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f437,plain,
    ( spl7_62
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f167,plain,
    ( spl7_16
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f274,plain,
    ( ! [X1] :
        ( v2_struct_0(sK6)
        | k16_lattice3(sK6,X1) = k15_lattice3(sK6,a_2_1_lattice3(sK6,X1)) )
    | ~ spl7_16 ),
    inference(resolution,[],[f80,f168])).

fof(f168,plain,
    ( l3_lattices(sK6)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f421,plain,
    ( ~ spl7_57
    | spl7_58
    | spl7_47 ),
    inference(avatar_split_clause,[],[f348,f344,f419,f413])).

fof(f413,plain,
    ( spl7_57
  <=> ~ m1_subset_1(sK1,sK4(k16_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f344,plain,
    ( spl7_47
  <=> ~ r2_hidden(sK1,sK4(k16_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f348,plain,
    ( v1_xboole_0(sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ m1_subset_1(sK1,sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_47 ),
    inference(resolution,[],[f345,f89])).

fof(f345,plain,
    ( ~ r2_hidden(sK1,sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f344])).

fof(f384,plain,
    ( spl7_48
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f371,f249,f350])).

fof(f350,plain,
    ( spl7_48
  <=> m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f249,plain,
    ( spl7_32
  <=> r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f371,plain,
    ( m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_32 ),
    inference(resolution,[],[f250,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t1_subset)).

fof(f250,plain,
    ( r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f249])).

fof(f381,plain,
    ( ~ spl7_55
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f370,f249,f379])).

fof(f370,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_32 ),
    inference(resolution,[],[f250,f91])).

fof(f374,plain,
    ( ~ spl7_32
    | spl7_49 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f371,f354])).

fof(f354,plain,
    ( ~ m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl7_49
  <=> ~ m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f369,plain,
    ( spl7_52
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f271,f255,f367])).

fof(f367,plain,
    ( spl7_52
  <=> m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f255,plain,
    ( spl7_34
  <=> r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f271,plain,
    ( m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2))
    | ~ spl7_34 ),
    inference(resolution,[],[f256,f90])).

fof(f256,plain,
    ( r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f255])).

fof(f362,plain,
    ( ~ spl7_51
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f270,f255,f360])).

fof(f270,plain,
    ( ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(sK1,k16_lattice3(sK0,sK2)))
    | ~ spl7_34 ),
    inference(resolution,[],[f256,f91])).

fof(f355,plain,
    ( ~ spl7_49
    | spl7_38
    | spl7_33 ),
    inference(avatar_split_clause,[],[f262,f252,f289,f353])).

fof(f289,plain,
    ( spl7_38
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f252,plain,
    ( spl7_33
  <=> ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f262,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_33 ),
    inference(resolution,[],[f253,f89])).

fof(f253,plain,
    ( ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f252])).

fof(f347,plain,
    ( spl7_40
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f334,f224,f307])).

fof(f307,plain,
    ( spl7_40
  <=> m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f224,plain,
    ( spl7_28
  <=> r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f334,plain,
    ( m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f225,f90])).

fof(f225,plain,
    ( r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f346,plain,
    ( ~ spl7_47
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f333,f224,f344])).

fof(f333,plain,
    ( ~ r2_hidden(sK1,sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_28 ),
    inference(resolution,[],[f225,f91])).

fof(f337,plain,
    ( ~ spl7_28
    | spl7_41 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f334,f311])).

fof(f311,plain,
    ( ~ m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl7_41
  <=> ~ m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f331,plain,
    ( spl7_44
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f239,f218,f329])).

fof(f329,plain,
    ( spl7_44
  <=> m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f218,plain,
    ( spl7_26
  <=> r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f239,plain,
    ( m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2))
    | ~ spl7_26 ),
    inference(resolution,[],[f219,f90])).

fof(f219,plain,
    ( r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f324,plain,
    ( ~ spl7_43
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f238,f218,f322])).

fof(f238,plain,
    ( ~ r2_hidden(k16_lattice3(sK0,sK2),sK4(k16_lattice3(sK0,sK2),sK1))
    | ~ spl7_26 ),
    inference(resolution,[],[f219,f91])).

fof(f312,plain,
    ( ~ spl7_41
    | spl7_38
    | spl7_29 ),
    inference(avatar_split_clause,[],[f232,f227,f289,f310])).

fof(f227,plain,
    ( spl7_29
  <=> ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f232,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_29 ),
    inference(resolution,[],[f228,f89])).

fof(f228,plain,
    ( ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f227])).

fof(f291,plain,
    ( ~ spl7_37
    | spl7_38
    | spl7_25 ),
    inference(avatar_split_clause,[],[f230,f201,f289,f283])).

fof(f283,plain,
    ( spl7_37
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f201,plain,
    ( spl7_25
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f230,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK1)
    | ~ spl7_25 ),
    inference(resolution,[],[f202,f89])).

fof(f202,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f201])).

fof(f267,plain,
    ( spl7_15
    | spl7_33
    | spl7_35 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f265,f161])).

fof(f265,plain,
    ( k16_lattice3(sK0,sK2) = sK1
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f263,f253])).

fof(f263,plain,
    ( r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | k16_lattice3(sK0,sK2) = sK1
    | ~ spl7_35 ),
    inference(resolution,[],[f259,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t2_tarski)).

fof(f259,plain,
    ( ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl7_35
  <=> ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f260,plain,
    ( ~ spl7_33
    | ~ spl7_35
    | spl7_15 ),
    inference(avatar_split_clause,[],[f212,f160,f258,f252])).

fof(f212,plain,
    ( ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,sK2))
    | ~ r2_hidden(sK4(sK1,k16_lattice3(sK0,sK2)),sK1)
    | ~ spl7_15 ),
    inference(extensionality_resolution,[],[f79,f161])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f247,plain,
    ( ~ spl7_31
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f240,f218,f245])).

fof(f245,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f240,plain,
    ( ~ v1_xboole_0(k16_lattice3(sK0,sK2))
    | ~ spl7_26 ),
    inference(resolution,[],[f219,f88])).

fof(f237,plain,
    ( spl7_15
    | spl7_27
    | spl7_29 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f235,f161])).

fof(f235,plain,
    ( k16_lattice3(sK0,sK2) = sK1
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f233,f228])).

fof(f233,plain,
    ( r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | k16_lattice3(sK0,sK2) = sK1
    | ~ spl7_27 ),
    inference(resolution,[],[f222,f78])).

fof(f222,plain,
    ( ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_27
  <=> ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f229,plain,
    ( ~ spl7_27
    | ~ spl7_29
    | spl7_15 ),
    inference(avatar_split_clause,[],[f211,f160,f227,f221])).

fof(f211,plain,
    ( ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ r2_hidden(sK4(k16_lattice3(sK0,sK2),sK1),k16_lattice3(sK0,sK2))
    | ~ spl7_15 ),
    inference(extensionality_resolution,[],[f79,f161])).

fof(f203,plain,
    ( ~ spl7_25
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f186,f139,f201])).

fof(f186,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_8 ),
    inference(resolution,[],[f91,f140])).

fof(f196,plain,
    ( spl7_22
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f185,f139,f194])).

fof(f194,plain,
    ( spl7_22
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f185,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f90,f140])).

fof(f184,plain,
    ( ~ spl7_21
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f177,f139,f182])).

fof(f182,plain,
    ( spl7_21
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f177,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f88,f140])).

fof(f176,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f83,f174])).

fof(f174,plain,
    ( spl7_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f83,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',d2_xboole_0)).

fof(f169,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f97,f167])).

fof(f97,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',existence_l3_lattices)).

fof(f162,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f67,f160])).

fof(f67,plain,(
    k16_lattice3(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t42_lattice3.p',t42_lattice3)).

fof(f155,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f68,f153])).

fof(f68,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f148,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f66,f146])).

fof(f66,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f141,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f65,f139])).

fof(f65,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f72,f132])).

fof(f72,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f71,f125])).

fof(f71,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f70,f118])).

fof(f70,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f69,f111])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
