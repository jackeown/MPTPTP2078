%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1505+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 7.16s
% Output     : Refutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 326 expanded)
%              Number of leaves         :   29 ( 134 expanded)
%              Depth                    :   17
%              Number of atoms          :  790 (1605 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6625,f6630,f6635,f6640,f6645,f6650,f6655,f6791,f6796,f6806,f8177,f8199,f13103,f13143])).

fof(f13143,plain,
    ( spl421_2
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_15
    | ~ spl421_171 ),
    inference(avatar_contradiction_clause,[],[f13142])).

fof(f13142,plain,
    ( $false
    | spl421_2
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_15
    | ~ spl421_171 ),
    inference(subsumption_resolution,[],[f13141,f6805])).

fof(f6805,plain,
    ( v6_lattices(sK0)
    | ~ spl421_15 ),
    inference(avatar_component_clause,[],[f6803])).

fof(f6803,plain,
    ( spl421_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_15])])).

fof(f13141,plain,
    ( ~ v6_lattices(sK0)
    | spl421_2
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_171 ),
    inference(unit_resulting_resolution,[],[f6654,f6795,f6790,f6639,f6634,f6668,f8176,f6624,f4620])).

fof(f4620,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3926])).

fof(f3926,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3010])).

fof(f3010,plain,(
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
    inference(flattening,[],[f3009])).

fof(f3009,plain,(
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
    inference(ennf_transformation,[],[f2057])).

fof(f2057,axiom,(
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

fof(f6624,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl421_2 ),
    inference(avatar_component_clause,[],[f6622])).

fof(f6622,plain,
    ( spl421_2
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_2])])).

fof(f8176,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ spl421_171 ),
    inference(avatar_component_clause,[],[f8174])).

fof(f8174,plain,
    ( spl421_171
  <=> r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_171])])).

fof(f6668,plain,
    ( ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
    | ~ spl421_5
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6639,f6654,f4397])).

fof(f4397,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2947])).

fof(f2947,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2946])).

fof(f2946,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2838])).

fof(f2838,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f6634,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl421_4 ),
    inference(avatar_component_clause,[],[f6632])).

fof(f6632,plain,
    ( spl421_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_4])])).

fof(f6639,plain,
    ( l3_lattices(sK0)
    | ~ spl421_5 ),
    inference(avatar_component_clause,[],[f6637])).

fof(f6637,plain,
    ( spl421_5
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_5])])).

fof(f6790,plain,
    ( v9_lattices(sK0)
    | ~ spl421_12 ),
    inference(avatar_component_clause,[],[f6788])).

fof(f6788,plain,
    ( spl421_12
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_12])])).

fof(f6795,plain,
    ( v8_lattices(sK0)
    | ~ spl421_13 ),
    inference(avatar_component_clause,[],[f6793])).

fof(f6793,plain,
    ( spl421_13
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_13])])).

fof(f6654,plain,
    ( ~ v2_struct_0(sK0)
    | spl421_8 ),
    inference(avatar_component_clause,[],[f6652])).

fof(f6652,plain,
    ( spl421_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_8])])).

fof(f13103,plain,
    ( spl421_1
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_15
    | ~ spl421_174 ),
    inference(avatar_contradiction_clause,[],[f13102])).

fof(f13102,plain,
    ( $false
    | spl421_1
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_15
    | ~ spl421_174 ),
    inference(subsumption_resolution,[],[f13074,f6805])).

fof(f13074,plain,
    ( ~ v6_lattices(sK0)
    | spl421_1
    | ~ spl421_4
    | ~ spl421_5
    | spl421_8
    | ~ spl421_12
    | ~ spl421_13
    | ~ spl421_174 ),
    inference(unit_resulting_resolution,[],[f6654,f6795,f6790,f6639,f6634,f6620,f6669,f8198,f4620])).

fof(f8198,plain,
    ( r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl421_174 ),
    inference(avatar_component_clause,[],[f8196])).

fof(f8196,plain,
    ( spl421_174
  <=> r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_174])])).

fof(f6669,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | ~ spl421_5
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6639,f6654,f4513])).

fof(f4513,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2959])).

fof(f2959,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2958])).

fof(f2958,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2837])).

fof(f2837,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f6620,plain,
    ( ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl421_1 ),
    inference(avatar_component_clause,[],[f6618])).

fof(f6618,plain,
    ( spl421_1
  <=> r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_1])])).

fof(f8199,plain,
    ( spl421_174
    | ~ spl421_3
    | ~ spl421_4
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(avatar_split_clause,[],[f8181,f6652,f6647,f6642,f6637,f6632,f6627,f8196])).

fof(f6627,plain,
    ( spl421_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_3])])).

fof(f6642,plain,
    ( spl421_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_6])])).

fof(f6647,plain,
    ( spl421_7
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl421_7])])).

fof(f8181,plain,
    ( r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl421_3
    | ~ spl421_4
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6654,f6639,f6629,f6634,f6669,f7188,f4640])).

fof(f4640,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X4,X1) ) ),
    inference(cnf_transformation,[],[f3940])).

fof(f3940,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK38(X0,X1,X2),X1)
                  & r2_hidden(sK38(X0,X1,X2),X2)
                  & m1_subset_1(sK38(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38])],[f3938,f3939])).

fof(f3939,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK38(X0,X1,X2),X1)
        & r2_hidden(sK38(X0,X1,X2),X2)
        & m1_subset_1(sK38(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3938,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3937])).

fof(f3937,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3029])).

fof(f3029,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3028])).

fof(f3028,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2816])).

fof(f2816,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f7188,plain,
    ( ! [X182] : r4_lattice3(sK0,k15_lattice3(sK0,X182),X182)
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7187,f6649])).

fof(f6649,plain,
    ( v10_lattices(sK0)
    | ~ spl421_7 ),
    inference(avatar_component_clause,[],[f6647])).

fof(f7187,plain,
    ( ! [X182] :
        ( ~ v10_lattices(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X182),X182) )
    | ~ spl421_5
    | ~ spl421_6
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7186,f6644])).

fof(f6644,plain,
    ( v4_lattice3(sK0)
    | ~ spl421_6 ),
    inference(avatar_component_clause,[],[f6642])).

fof(f7186,plain,
    ( ! [X182] :
        ( ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X182),X182) )
    | ~ spl421_5
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7185,f6639])).

fof(f7185,plain,
    ( ! [X182] :
        ( ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X182),X182) )
    | ~ spl421_5
    | spl421_8 ),
    inference(subsumption_resolution,[],[f6778,f6669])).

fof(f6778,plain,
    ( ! [X182] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X182),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X182),X182) )
    | spl421_8 ),
    inference(resolution,[],[f6654,f6586])).

fof(f6586,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f6063])).

fof(f6063,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4514])).

fof(f4514,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3870])).

fof(f3870,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK10(X0,X1,X2))
                & r4_lattice3(X0,sK10(X0,X1,X2),X1)
                & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f3868,f3869])).

fof(f3869,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK10(X0,X1,X2))
        & r4_lattice3(X0,sK10(X0,X1,X2),X1)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3868,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3867])).

fof(f3867,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3866])).

fof(f3866,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2961])).

fof(f2961,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2960])).

fof(f2960,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2821])).

fof(f2821,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f6629,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl421_3 ),
    inference(avatar_component_clause,[],[f6627])).

fof(f8177,plain,
    ( spl421_171
    | ~ spl421_3
    | ~ spl421_4
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(avatar_split_clause,[],[f8159,f6652,f6647,f6642,f6637,f6632,f6627,f8174])).

fof(f8159,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ spl421_3
    | ~ spl421_4
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6654,f6639,f6629,f6634,f6668,f7158,f4544])).

fof(f4544,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X4) ) ),
    inference(cnf_transformation,[],[f3893])).

fof(f3893,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK18(X0,X1,X2))
                  & r2_hidden(sK18(X0,X1,X2),X2)
                  & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f3891,f3892])).

fof(f3892,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK18(X0,X1,X2))
        & r2_hidden(sK18(X0,X1,X2),X2)
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3891,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3890])).

fof(f3890,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2980])).

fof(f2980,plain,(
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
    inference(flattening,[],[f2979])).

fof(f2979,plain,(
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
    inference(ennf_transformation,[],[f2815])).

fof(f2815,axiom,(
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

fof(f7158,plain,
    ( ! [X167] : r3_lattice3(sK0,k16_lattice3(sK0,X167),X167)
    | ~ spl421_5
    | ~ spl421_6
    | ~ spl421_7
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7157,f6649])).

fof(f7157,plain,
    ( ! [X167] :
        ( ~ v10_lattices(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X167),X167) )
    | ~ spl421_5
    | ~ spl421_6
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7156,f6644])).

fof(f7156,plain,
    ( ! [X167] :
        ( ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X167),X167) )
    | ~ spl421_5
    | spl421_8 ),
    inference(subsumption_resolution,[],[f7155,f6639])).

fof(f7155,plain,
    ( ! [X167] :
        ( ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X167),X167) )
    | ~ spl421_5
    | spl421_8 ),
    inference(subsumption_resolution,[],[f6770,f6668])).

fof(f6770,plain,
    ( ! [X167] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X167),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | r3_lattice3(sK0,k16_lattice3(sK0,X167),X167) )
    | spl421_8 ),
    inference(resolution,[],[f6654,f6061])).

fof(f6061,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f4398])).

fof(f4398,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3852])).

fof(f3852,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3850,f3851])).

fof(f3851,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3850,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3849])).

fof(f3849,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3848])).

fof(f3848,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2949])).

fof(f2949,plain,(
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
    inference(flattening,[],[f2948])).

fof(f2948,plain,(
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
    inference(ennf_transformation,[],[f2915])).

fof(f2915,axiom,(
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

fof(f6806,plain,
    ( spl421_15
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(avatar_split_clause,[],[f6674,f6652,f6647,f6637,f6803])).

fof(f6674,plain,
    ( v6_lattices(sK0)
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6639,f6649,f6654,f4818])).

fof(f4818,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f3109,plain,(
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
    inference(flattening,[],[f3108])).

fof(f3108,plain,(
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
    inference(ennf_transformation,[],[f2010])).

fof(f2010,axiom,(
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

fof(f6796,plain,
    ( spl421_13
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(avatar_split_clause,[],[f6676,f6652,f6647,f6637,f6793])).

fof(f6676,plain,
    ( v8_lattices(sK0)
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6639,f6649,f6654,f4820])).

fof(f4820,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f6791,plain,
    ( spl421_12
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(avatar_split_clause,[],[f6677,f6652,f6647,f6637,f6788])).

fof(f6677,plain,
    ( v9_lattices(sK0)
    | ~ spl421_5
    | ~ spl421_7
    | spl421_8 ),
    inference(unit_resulting_resolution,[],[f6639,f6649,f6654,f4821])).

fof(f4821,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f6655,plain,(
    ~ spl421_8 ),
    inference(avatar_split_clause,[],[f4390,f6652])).

fof(f4390,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3847])).

fof(f3847,plain,
    ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
      | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) )
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2945,f3846,f3845,f3844])).

fof(f3844,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),X1)
                | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3845,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),X1)
              | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,X2)) )
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
            | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,X2)) )
          & r2_hidden(sK1,X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3846,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
          | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,X2)) )
        & r2_hidden(sK1,X2) )
   => ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
        | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) )
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2945,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2944])).

fof(f2944,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2920])).

fof(f2920,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f2919])).

fof(f2919,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f6650,plain,(
    spl421_7 ),
    inference(avatar_split_clause,[],[f4391,f6647])).

fof(f4391,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f3847])).

fof(f6645,plain,(
    spl421_6 ),
    inference(avatar_split_clause,[],[f4392,f6642])).

fof(f4392,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3847])).

fof(f6640,plain,(
    spl421_5 ),
    inference(avatar_split_clause,[],[f4393,f6637])).

fof(f4393,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f3847])).

fof(f6635,plain,(
    spl421_4 ),
    inference(avatar_split_clause,[],[f4394,f6632])).

fof(f4394,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3847])).

fof(f6630,plain,(
    spl421_3 ),
    inference(avatar_split_clause,[],[f4395,f6627])).

fof(f4395,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f3847])).

fof(f6625,plain,
    ( ~ spl421_1
    | ~ spl421_2 ),
    inference(avatar_split_clause,[],[f4396,f6622,f6618])).

fof(f4396,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f3847])).
%------------------------------------------------------------------------------
