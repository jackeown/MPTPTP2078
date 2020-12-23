%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:44 EST 2020

% Result     : Theorem 4.87s
% Output     : Refutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :  449 (1177 expanded)
%              Number of leaves         :   77 ( 512 expanded)
%              Depth                    :   17
%              Number of atoms          : 2687 (6075 expanded)
%              Number of equality atoms :  226 ( 559 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f153,f161,f170,f187,f191,f216,f223,f235,f255,f259,f267,f279,f283,f292,f307,f321,f348,f381,f385,f405,f476,f606,f678,f735,f875,f1104,f1142,f1411,f1446,f1508,f1512,f1573,f1625,f1659,f1678,f3565,f3881,f3985,f4025,f4236,f4444,f4533,f4593,f4634,f5187,f6850,f6857,f6866,f7116,f8553,f8643,f8658])).

fof(f8658,plain,
    ( spl9_1
    | ~ spl9_4
    | ~ spl9_26
    | ~ spl9_27
    | spl9_447
    | ~ spl9_530 ),
    inference(avatar_contradiction_clause,[],[f8657])).

fof(f8657,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | ~ spl9_26
    | ~ spl9_27
    | spl9_447
    | ~ spl9_530 ),
    inference(subsumption_resolution,[],[f8656,f109])).

fof(f109,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f8656,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_26
    | ~ spl9_27
    | spl9_447
    | ~ spl9_530 ),
    inference(subsumption_resolution,[],[f8655,f124])).

fof(f124,plain,
    ( l3_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f8655,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_26
    | ~ spl9_27
    | spl9_447
    | ~ spl9_530 ),
    inference(subsumption_resolution,[],[f8654,f7115])).

fof(f7115,plain,
    ( ~ r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | spl9_447 ),
    inference(avatar_component_clause,[],[f7113])).

fof(f7113,plain,
    ( spl9_447
  <=> r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).

fof(f8654,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_26
    | ~ spl9_27
    | ~ spl9_530 ),
    inference(subsumption_resolution,[],[f8653,f290])).

fof(f290,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl9_27
  <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f8653,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_26
    | ~ spl9_530 ),
    inference(subsumption_resolution,[],[f8650,f287])).

fof(f287,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_26
  <=> r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f8650,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_530 ),
    inference(duplicate_literal_removal,[],[f8649])).

fof(f8649,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_530 ),
    inference(resolution,[],[f8642,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK6(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f8642,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_530 ),
    inference(avatar_component_clause,[],[f8641])).

fof(f8641,plain,
    ( spl9_530
  <=> ! [X0] :
        ( r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_530])])).

fof(f8643,plain,
    ( spl9_530
    | ~ spl9_27
    | ~ spl9_124
    | spl9_447
    | ~ spl9_523 ),
    inference(avatar_split_clause,[],[f8584,f8550,f7113,f1444,f289,f8641])).

fof(f1444,plain,
    ( spl9_124
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f8550,plain,
    ( spl9_523
  <=> sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_523])])).

fof(f8584,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_27
    | ~ spl9_124
    | spl9_447
    | ~ spl9_523 ),
    inference(subsumption_resolution,[],[f8583,f7115])).

fof(f8583,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) )
    | ~ spl9_27
    | ~ spl9_124
    | ~ spl9_523 ),
    inference(subsumption_resolution,[],[f8569,f290])).

fof(f8569,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
        | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) )
    | ~ spl9_124
    | ~ spl9_523 ),
    inference(superposition,[],[f1445,f8552])).

fof(f8552,plain,
    ( sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_523 ),
    inference(avatar_component_clause,[],[f8550])).

fof(f1445,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) )
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f8553,plain,
    ( spl9_523
    | ~ spl9_27
    | ~ spl9_58
    | spl9_447 ),
    inference(avatar_split_clause,[],[f7125,f7113,f604,f289,f8550])).

fof(f604,plain,
    ( spl9_58
  <=> ! [X1,X0] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f7125,plain,
    ( sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_27
    | ~ spl9_58
    | spl9_447 ),
    inference(subsumption_resolution,[],[f7119,f290])).

fof(f7119,plain,
    ( sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_58
    | spl9_447 ),
    inference(resolution,[],[f7115,f605])).

fof(f605,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f604])).

fof(f7116,plain,
    ( ~ spl9_447
    | spl9_24
    | ~ spl9_27
    | ~ spl9_344 ),
    inference(avatar_split_clause,[],[f7100,f5185,f289,f276,f7113])).

fof(f276,plain,
    ( spl9_24
  <=> r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f5185,plain,
    ( spl9_344
  <=> ! [X2] :
        ( r3_lattices(sK0,X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_344])])).

fof(f7100,plain,
    ( ~ r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | spl9_24
    | ~ spl9_27
    | ~ spl9_344 ),
    inference(subsumption_resolution,[],[f7076,f278])).

fof(f278,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f276])).

fof(f7076,plain,
    ( r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | ~ r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ spl9_27
    | ~ spl9_344 ),
    inference(resolution,[],[f5186,f290])).

fof(f5186,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,X2,sK1)
        | ~ r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) )
    | ~ spl9_344 ),
    inference(avatar_component_clause,[],[f5185])).

fof(f6866,plain,
    ( spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | spl9_299
    | ~ spl9_416 ),
    inference(avatar_contradiction_clause,[],[f6865])).

fof(f6865,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | spl9_299
    | ~ spl9_416 ),
    inference(subsumption_resolution,[],[f6864,f109])).

fof(f6864,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | spl9_299
    | ~ spl9_416 ),
    inference(subsumption_resolution,[],[f6863,f124])).

fof(f6863,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | spl9_299
    | ~ spl9_416 ),
    inference(subsumption_resolution,[],[f6862,f134])).

fof(f134,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f6862,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_299
    | ~ spl9_416 ),
    inference(subsumption_resolution,[],[f6860,f4050])).

fof(f4050,plain,
    ( ~ r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | spl9_299 ),
    inference(avatar_component_clause,[],[f4049])).

fof(f4049,plain,
    ( spl9_299
  <=> r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).

fof(f6860,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_416 ),
    inference(resolution,[],[f6497,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f6497,plain,
    ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)
    | ~ spl9_416 ),
    inference(avatar_component_clause,[],[f6495])).

fof(f6495,plain,
    ( spl9_416
  <=> r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_416])])).

fof(f6857,plain,
    ( spl9_416
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_441 ),
    inference(avatar_split_clause,[],[f6855,f6848,f132,f127,f6495])).

fof(f127,plain,
    ( spl9_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f6848,plain,
    ( spl9_441
  <=> ! [X0] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_441])])).

fof(f6855,plain,
    ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_441 ),
    inference(subsumption_resolution,[],[f6852,f134])).

fof(f6852,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)
    | ~ spl9_5
    | ~ spl9_441 ),
    inference(resolution,[],[f6849,f129])).

fof(f129,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f6849,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) )
    | ~ spl9_441 ),
    inference(avatar_component_clause,[],[f6848])).

fof(f6850,plain,
    ( spl9_441
    | ~ spl9_6
    | ~ spl9_119
    | ~ spl9_295
    | spl9_299 ),
    inference(avatar_split_clause,[],[f6842,f4049,f4018,f1409,f132,f6848])).

fof(f1409,plain,
    ( spl9_119
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f4018,plain,
    ( spl9_295
  <=> sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_295])])).

fof(f6842,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_6
    | ~ spl9_119
    | ~ spl9_295
    | spl9_299 ),
    inference(subsumption_resolution,[],[f4039,f4050])).

fof(f4039,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) )
    | ~ spl9_6
    | ~ spl9_119
    | ~ spl9_295 ),
    inference(subsumption_resolution,[],[f4031,f134])).

fof(f4031,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl9_119
    | ~ spl9_295 ),
    inference(superposition,[],[f1410,f4020])).

fof(f4020,plain,
    ( sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2)
    | ~ spl9_295 ),
    inference(avatar_component_clause,[],[f4018])).

fof(f1410,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_119 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f5187,plain,
    ( spl9_344
    | ~ spl9_17
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f4659,f4437,f221,f5185])).

fof(f221,plain,
    ( spl9_17
  <=> ! [X1,X0] :
        ( r3_lattices(sK0,X1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f4437,plain,
    ( spl9_318
  <=> sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_318])])).

fof(f4659,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) )
    | ~ spl9_17
    | ~ spl9_318 ),
    inference(superposition,[],[f222,f4439])).

fof(f4439,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_318 ),
    inference(avatar_component_clause,[],[f4437])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0)) )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f221])).

fof(f4634,plain,
    ( spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_11
    | spl9_319
    | ~ spl9_322
    | ~ spl9_324 ),
    inference(avatar_contradiction_clause,[],[f4629])).

fof(f4629,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_11
    | spl9_319
    | ~ spl9_322
    | ~ spl9_324 ),
    inference(unit_resulting_resolution,[],[f109,f124,f134,f169,f4443,f4475,f4592,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4592,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | ~ spl9_324 ),
    inference(avatar_component_clause,[],[f4590])).

fof(f4590,plain,
    ( spl9_324
  <=> r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_324])])).

fof(f4475,plain,
    ( m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl9_322 ),
    inference(avatar_component_clause,[],[f4474])).

fof(f4474,plain,
    ( spl9_322
  <=> m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).

fof(f4443,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | spl9_319 ),
    inference(avatar_component_clause,[],[f4441])).

fof(f4441,plain,
    ( spl9_319
  <=> r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).

fof(f169,plain,
    ( r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl9_11
  <=> r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f4593,plain,
    ( spl9_318
    | spl9_324
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(avatar_split_clause,[],[f4347,f4049,f132,f122,f117,f112,f107,f4590,f4437])).

fof(f112,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f117,plain,
    ( spl9_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f4347,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4346,f109])).

fof(f4346,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4345,f114])).

fof(f114,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f4345,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4344,f119])).

fof(f119,plain,
    ( v4_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f4344,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4343,f124])).

fof(f4343,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4335,f134])).

fof(f4335,plain,
    ( r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_299 ),
    inference(resolution,[],[f4051,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X2,X1)
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | k15_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f4051,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_299 ),
    inference(avatar_component_clause,[],[f4049])).

fof(f4533,plain,
    ( spl9_318
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(avatar_split_clause,[],[f4512,f4474,f4049,f132,f122,f117,f112,f107,f4437])).

fof(f4512,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4511,f109])).

fof(f4511,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4510,f114])).

fof(f4510,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4509,f119])).

fof(f4509,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4508,f124])).

fof(f4508,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4507,f134])).

fof(f4507,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_299
    | spl9_322 ),
    inference(subsumption_resolution,[],[f4506,f4051])).

fof(f4506,plain,
    ( sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_322 ),
    inference(resolution,[],[f4476,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k15_lattice3(X0,X1) = X2
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4476,plain,
    ( ~ m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl9_322 ),
    inference(avatar_component_clause,[],[f4474])).

fof(f4444,plain,
    ( spl9_318
    | ~ spl9_319
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(avatar_split_clause,[],[f4342,f4049,f132,f122,f117,f112,f107,f4441,f4437])).

fof(f4342,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4341,f109])).

fof(f4341,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4340,f114])).

fof(f4340,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4339,f119])).

fof(f4339,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4338,f124])).

fof(f4338,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_299 ),
    inference(subsumption_resolution,[],[f4334,f134])).

fof(f4334,plain,
    ( ~ r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))
    | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_299 ),
    inference(resolution,[],[f4051,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X2,X1)
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4236,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_139
    | ~ spl9_296
    | spl9_299 ),
    inference(avatar_contradiction_clause,[],[f4235])).

fof(f4235,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_139
    | ~ spl9_296
    | spl9_299 ),
    inference(subsumption_resolution,[],[f4116,f4050])).

fof(f4116,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_139
    | ~ spl9_296 ),
    inference(forward_demodulation,[],[f4115,f1677])).

fof(f1677,plain,
    ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_139 ),
    inference(avatar_component_clause,[],[f1675])).

fof(f1675,plain,
    ( spl9_139
  <=> sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f4115,plain,
    ( r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_296 ),
    inference(subsumption_resolution,[],[f4114,f109])).

fof(f4114,plain,
    ( r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_296 ),
    inference(subsumption_resolution,[],[f4113,f114])).

fof(f4113,plain,
    ( r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_296 ),
    inference(subsumption_resolution,[],[f4112,f119])).

fof(f4112,plain,
    ( r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_296 ),
    inference(subsumption_resolution,[],[f4100,f124])).

fof(f4100,plain,
    ( r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_296 ),
    inference(resolution,[],[f4024,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | r4_lattice3(X1,sK7(X0,X1,X2),X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK7(X0,X1,X2),X2)
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK7(X0,X1,X2),X2)
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f4024,plain,
    ( r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | ~ spl9_296 ),
    inference(avatar_component_clause,[],[f4022])).

fof(f4022,plain,
    ( spl9_296
  <=> r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_296])])).

fof(f4025,plain,
    ( spl9_295
    | spl9_296
    | ~ spl9_139
    | ~ spl9_293 ),
    inference(avatar_split_clause,[],[f3999,f3983,f1675,f4022,f4018])).

fof(f3983,plain,
    ( spl9_293
  <=> ! [X1] :
        ( r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).

fof(f3999,plain,
    ( r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))
    | sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2)
    | ~ spl9_139
    | ~ spl9_293 ),
    inference(superposition,[],[f3984,f1677])).

fof(f3984,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) )
    | ~ spl9_293 ),
    inference(avatar_component_clause,[],[f3983])).

fof(f3985,plain,
    ( spl9_293
    | ~ spl9_6
    | ~ spl9_290 ),
    inference(avatar_split_clause,[],[f3941,f3879,f132,f3983])).

fof(f3879,plain,
    ( spl9_290
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_290])])).

fof(f3941,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) )
    | ~ spl9_6
    | ~ spl9_290 ),
    inference(resolution,[],[f3880,f134])).

fof(f3880,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) )
    | ~ spl9_290 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f3881,plain,
    ( spl9_290
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59
    | ~ spl9_280 ),
    inference(avatar_split_clause,[],[f3849,f3563,f676,f122,f117,f112,f107,f3879])).

fof(f676,plain,
    ( spl9_59
  <=> ! [X7,X8] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f3563,plain,
    ( spl9_280
  <=> ! [X7,X8] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).

fof(f3849,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59
    | ~ spl9_280 ),
    inference(subsumption_resolution,[],[f3848,f677])).

fof(f677,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f676])).

fof(f3848,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_280 ),
    inference(subsumption_resolution,[],[f3847,f109])).

fof(f3847,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_280 ),
    inference(subsumption_resolution,[],[f3846,f114])).

fof(f3846,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_280 ),
    inference(subsumption_resolution,[],[f3845,f119])).

fof(f3845,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_280 ),
    inference(subsumption_resolution,[],[f3816,f124])).

fof(f3816,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_280 ),
    inference(resolution,[],[f3564,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3564,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) )
    | ~ spl9_280 ),
    inference(avatar_component_clause,[],[f3563])).

fof(f3565,plain,
    ( spl9_280
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_128 ),
    inference(avatar_split_clause,[],[f1569,f1510,f122,f117,f112,f107,f3563])).

fof(f1510,plain,
    ( spl9_128
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f1569,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1568,f109])).

fof(f1568,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1567,f114])).

fof(f1567,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1566,f119])).

fof(f1566,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1553,f124])).

fof(f1553,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_128 ),
    inference(resolution,[],[f1511,f99])).

fof(f99,plain,(
    ! [X2,X3,X1] :
      ( ~ r4_lattice3(X1,X3,X2)
      | r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1511,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_128 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1678,plain,
    ( spl9_139
    | ~ spl9_5
    | ~ spl9_137 ),
    inference(avatar_split_clause,[],[f1660,f1657,f127,f1675])).

fof(f1657,plain,
    ( spl9_137
  <=> ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f1660,plain,
    ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_5
    | ~ spl9_137 ),
    inference(resolution,[],[f1658,f129])).

fof(f1658,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK1,X5)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) )
    | ~ spl9_137 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f1659,plain,
    ( spl9_137
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1648,f1623,f122,f117,f112,f107,f1657])).

fof(f1623,plain,
    ( spl9_136
  <=> ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1648,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1647,f109])).

fof(f1647,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1646,f114])).

fof(f1646,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1645,f119])).

fof(f1645,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f1638,f124])).

fof(f1638,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_136 ),
    inference(duplicate_literal_removal,[],[f1637])).

fof(f1637,plain,
    ( ! [X5] :
        ( sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ r2_hidden(sK1,X5)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_136 ),
    inference(resolution,[],[f1624,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sK7(X0,X1,X2) = X0
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1624,plain,
    ( ! [X4] :
        ( r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | ~ r2_hidden(sK1,X4) )
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f1625,plain,
    ( spl9_136
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(avatar_split_clause,[],[f1601,f1571,f132,f122,f117,f112,f107,f1623])).

fof(f1571,plain,
    ( spl9_135
  <=> ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f1601,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f1600,f109])).

fof(f1600,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f1599,f114])).

fof(f1599,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f1598,f119])).

fof(f1598,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f1597,f124])).

fof(f1597,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_6
    | ~ spl9_135 ),
    inference(subsumption_resolution,[],[f1583,f134])).

fof(f1583,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_135 ),
    inference(resolution,[],[f1572,f99])).

fof(f1572,plain,
    ( ! [X4] :
        ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | ~ r2_hidden(sK1,X4)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) )
    | ~ spl9_135 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1573,plain,
    ( spl9_135
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_127 ),
    inference(avatar_split_clause,[],[f1546,f1506,f132,f122,f107,f1571])).

fof(f1506,plain,
    ( spl9_127
  <=> ! [X1,X0] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f1546,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f1545,f109])).

fof(f1545,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f1544,f124])).

fof(f1544,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_6
    | ~ spl9_127 ),
    inference(subsumption_resolution,[],[f1541,f134])).

fof(f1541,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_127 ),
    inference(duplicate_literal_removal,[],[f1539])).

fof(f1539,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X4)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_127 ),
    inference(resolution,[],[f1507,f82])).

fof(f1507,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0)) )
    | ~ spl9_127 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1512,plain,
    ( spl9_128
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(avatar_split_clause,[],[f696,f676,f122,f117,f112,f107,f1510])).

fof(f696,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f695,f109])).

fof(f695,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f694,f114])).

fof(f694,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f693,f119])).

fof(f693,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f691,f124])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_59 ),
    inference(resolution,[],[f677,f89])).

fof(f1508,plain,
    ( spl9_127
    | ~ spl9_6
    | ~ spl9_80
    | ~ spl9_119 ),
    inference(avatar_split_clause,[],[f1471,f1409,f873,f132,f1506])).

fof(f873,plain,
    ( spl9_80
  <=> ! [X1] :
        ( sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f1471,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0)) )
    | ~ spl9_6
    | ~ spl9_80
    | ~ spl9_119 ),
    inference(subsumption_resolution,[],[f1468,f134])).

fof(f1468,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0)) )
    | ~ spl9_80
    | ~ spl9_119 ),
    inference(superposition,[],[f1410,f874])).

fof(f874,plain,
    ( ! [X1] :
        ( sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)) )
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f873])).

fof(f1446,plain,
    ( spl9_124
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_101 ),
    inference(avatar_split_clause,[],[f1200,f1140,f189,f122,f117,f112,f107,f1444])).

fof(f189,plain,
    ( spl9_14
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1140,plain,
    ( spl9_101
  <=> ! [X5,X4,X6] :
        ( r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5))
        | ~ m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f1200,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_101 ),
    inference(subsumption_resolution,[],[f1199,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1199,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))
        | ~ r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_101 ),
    inference(subsumption_resolution,[],[f1198,f109])).

fof(f1198,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))
        | ~ r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_101 ),
    inference(subsumption_resolution,[],[f1197,f114])).

fof(f1197,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))
        | ~ r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_101 ),
    inference(subsumption_resolution,[],[f1196,f119])).

fof(f1196,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))
        | ~ r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_101 ),
    inference(subsumption_resolution,[],[f1195,f124])).

fof(f1195,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2))
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))
        | ~ r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_101 ),
    inference(resolution,[],[f1141,f87])).

fof(f1141,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5))
        | r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5)) )
    | ~ spl9_101 ),
    inference(avatar_component_clause,[],[f1140])).

fof(f1411,plain,
    ( spl9_119
    | spl9_1
    | ~ spl9_4
    | ~ spl9_13
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f1151,f1102,f185,f122,f107,f1409])).

fof(f185,plain,
    ( spl9_13
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1102,plain,
    ( spl9_97
  <=> ! [X5,X4,X6] :
        ( r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f1151,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_13
    | ~ spl9_97 ),
    inference(subsumption_resolution,[],[f1150,f186])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1150,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1)
        | ~ r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_97 ),
    inference(subsumption_resolution,[],[f1149,f109])).

fof(f1149,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1)
        | ~ r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2))
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_97 ),
    inference(subsumption_resolution,[],[f1147,f124])).

fof(f1147,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2))
        | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1)
        | ~ r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_97 ),
    inference(resolution,[],[f1103,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK8(X0,X1,X2),X2)
            & sK8(X0,X1,X2) = X0
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK8(X0,X1,X2),X2)
        & sK8(X0,X1,X2) = X0
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f1103,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5))
        | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6) )
    | ~ spl9_97 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1142,plain,
    ( spl9_101
    | spl9_1
    | ~ spl9_4
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f445,f403,f122,f107,f1140])).

fof(f403,plain,
    ( spl9_41
  <=> ! [X1,X0] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f445,plain,
    ( ! [X6,X4,X5] :
        ( r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5))
        | ~ m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f444,f109])).

fof(f444,plain,
    ( ! [X6,X4,X5] :
        ( r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5))
        | ~ m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f434,f124])).

fof(f434,plain,
    ( ! [X6,X4,X5] :
        ( r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5))
        | ~ m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_41 ),
    inference(resolution,[],[f404,f79])).

fof(f404,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f403])).

fof(f1104,plain,
    ( spl9_97
    | ~ spl9_18
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f408,f379,f233,f1102])).

fof(f233,plain,
    ( spl9_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f379,plain,
    ( spl9_37
  <=> ! [X1,X0] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f408,plain,
    ( ! [X6,X4,X5] :
        ( r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,X5)
        | ~ m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))
        | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6) )
    | ~ spl9_18
    | ~ spl9_37 ),
    inference(resolution,[],[f380,f234])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X0) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f233])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f379])).

fof(f875,plain,
    ( spl9_80
    | ~ spl9_6
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f843,f733,f132,f873])).

fof(f733,plain,
    ( spl9_64
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f843,plain,
    ( ! [X1] :
        ( sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)) )
    | ~ spl9_6
    | ~ spl9_64 ),
    inference(resolution,[],[f734,f134])).

fof(f734,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 )
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f733])).

fof(f735,plain,
    ( spl9_64
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(avatar_split_clause,[],[f700,f676,f122,f117,f112,f107,f733])).

fof(f700,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f699,f109])).

fof(f699,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f698,f114])).

fof(f698,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f697,f119])).

fof(f697,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f692,f124])).

fof(f692,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3)
        | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_59 ),
    inference(resolution,[],[f677,f88])).

fof(f678,plain,
    ( spl9_59
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f631,f474,f122,f117,f112,f107,f676])).

fof(f474,plain,
    ( spl9_46
  <=> ! [X1,X0] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f631,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f630,f109])).

fof(f630,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f629,f114])).

fof(f629,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f628,f119])).

fof(f628,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f614,f124])).

fof(f614,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_46 ),
    inference(duplicate_literal_removal,[],[f613])).

fof(f613,plain,
    ( ! [X8,X7] :
        ( sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_46 ),
    inference(resolution,[],[f475,f99])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f474])).

fof(f606,plain,
    ( spl9_58
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f401,f383,f122,f117,f112,f107,f604])).

fof(f383,plain,
    ( spl9_38
  <=> ! [X9,X11,X10] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11))
        | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11)
        | ~ l3_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ v10_lattices(X10)
        | v2_struct_0(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f401,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f400,f109])).

fof(f400,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f399,f114])).

fof(f399,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f398,f124])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_38 ),
    inference(resolution,[],[f384,f119])).

fof(f384,plain,
    ( ! [X10,X11,X9] :
        ( ~ v4_lattice3(X10)
        | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11))
        | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ v10_lattices(X10)
        | v2_struct_0(X10) )
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f383])).

fof(f476,plain,
    ( spl9_46
    | spl9_1
    | ~ spl9_4
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f351,f319,f122,f107,f474])).

fof(f319,plain,
    ( spl9_29
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5))
        | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5)
        | ~ l3_lattices(X4)
        | v2_struct_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f350,f109])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_29 ),
    inference(resolution,[],[f320,f124])).

fof(f320,plain,
    ( ! [X4,X5,X3] :
        ( ~ l3_lattices(X4)
        | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5))
        | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(X4) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f319])).

fof(f405,plain,
    ( spl9_41
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f370,f346,f122,f117,f112,f107,f403])).

fof(f346,plain,
    ( spl9_34
  <=> ! [X7,X8,X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8))
        | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8)
        | ~ l3_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ v10_lattices(X7)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f369,f109])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f368,f114])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f367,f124])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1))
        | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_34 ),
    inference(resolution,[],[f347,f119])).

fof(f347,plain,
    ( ! [X6,X8,X7] :
        ( ~ v4_lattice3(X7)
        | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8))
        | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8)
        | ~ l3_lattices(X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v10_lattices(X7)
        | v2_struct_0(X7) )
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f346])).

fof(f385,plain,
    ( spl9_38
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f204,f189,f383])).

fof(f204,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11))
        | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11)
        | ~ l3_lattices(X10)
        | ~ v4_lattice3(X10)
        | ~ v10_lattices(X10)
        | v2_struct_0(X10) )
    | ~ spl9_14 ),
    inference(resolution,[],[f190,f88])).

fof(f381,plain,
    ( spl9_37
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f309,f281,f122,f107,f379])).

fof(f281,plain,
    ( spl9_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2))
        | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2)
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f308,f109])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
        | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(resolution,[],[f282,f124])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( ~ l3_lattices(X1)
        | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2))
        | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(X1) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f281])).

fof(f348,plain,
    ( spl9_34
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f203,f189,f346])).

fof(f203,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8))
        | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8)
        | ~ l3_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ v10_lattices(X7)
        | v2_struct_0(X7) )
    | ~ spl9_14 ),
    inference(resolution,[],[f190,f89])).

fof(f321,plain,
    ( spl9_29
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f198,f185,f319])).

fof(f198,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5))
        | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5)
        | ~ l3_lattices(X4)
        | v2_struct_0(X4) )
    | ~ spl9_13 ),
    inference(resolution,[],[f186,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sK8(X0,X1,X2) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f307,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f305,f109])).

fof(f305,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f304,f114])).

fof(f304,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f303,f119])).

fof(f303,plain,
    ( ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f302,f124])).

fof(f302,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f301,f134])).

fof(f301,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_7
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f300,f139])).

fof(f139,plain,
    ( r3_lattice3(sK0,sK1,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl9_7
  <=> r3_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f300,plain,
    ( ~ r3_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_8
    | spl9_27 ),
    inference(subsumption_resolution,[],[f298,f144])).

fof(f144,plain,
    ( sK1 != k16_lattice3(sK0,sK2)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_8
  <=> sK1 = k16_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f298,plain,
    ( sK1 = k16_lattice3(sK0,sK2)
    | ~ r3_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_27 ),
    inference(resolution,[],[f291,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f291,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f289])).

fof(f292,plain,
    ( spl9_26
    | ~ spl9_27
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f274,f264,f159,f289,f285])).

fof(f159,plain,
    ( spl9_10
  <=> ! [X1,X0] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f264,plain,
    ( spl9_23
  <=> r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f274,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2))
    | ~ spl9_10
    | ~ spl9_23 ),
    inference(resolution,[],[f266,f160])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f266,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f264])).

fof(f283,plain,
    ( spl9_25
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f197,f185,f281])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2))
        | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2)
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) )
    | ~ spl9_13 ),
    inference(resolution,[],[f186,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | r3_lattice3(X1,sK8(X0,X1,X2),X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f279,plain,
    ( ~ spl9_24
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f270,f257,f142,f137,f132,f276])).

fof(f257,plain,
    ( spl9_22
  <=> ! [X1,X0] :
        ( ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f270,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f269,f144])).

fof(f269,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | sK1 = k16_lattice3(sK0,sK2)
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f268,f134])).

fof(f268,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k16_lattice3(sK0,sK2)
    | ~ spl9_7
    | ~ spl9_22 ),
    inference(resolution,[],[f258,f139])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f257])).

fof(f267,plain,
    ( spl9_23
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f262,f253,f142,f137,f132,f264])).

fof(f253,plain,
    ( spl9_21
  <=> ! [X1,X0] :
        ( r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f262,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_8
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f261,f144])).

fof(f261,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | sK1 = k16_lattice3(sK0,sK2)
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f260,f134])).

fof(f260,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k16_lattice3(sK0,sK2)
    | ~ spl9_7
    | ~ spl9_21 ),
    inference(resolution,[],[f254,f139])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f253])).

fof(f259,plain,
    ( spl9_22
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f231,f122,f117,f112,f107,f257])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f230,f109])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f229,f114])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f228,f124])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,sK3(sK0,X0,X1),X0)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k16_lattice3(sK0,X1) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f73,f119])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f255,plain,
    ( spl9_21
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f227,f122,f117,f112,f107,f253])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f226,f109])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f225,f114])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k16_lattice3(sK0,X1) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f224,f124])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( r3_lattice3(sK0,sK3(sK0,X0,X1),X1)
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k16_lattice3(sK0,X1) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f72,f119])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f235,plain,
    ( spl9_18
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f219,f122,f107,f233])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X0) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f218,f109])).

fof(f218,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,X2,X0)
        | v2_struct_0(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f83,f124])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f223,plain,
    ( spl9_17
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f217,f214,f151,f221])).

fof(f151,plain,
    ( spl9_9
  <=> ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f214,plain,
    ( spl9_16
  <=> ! [X1,X0] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0)) )
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(superposition,[],[f215,f152])).

fof(f152,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( spl9_16
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f212,f122,f117,f112,f107,f214])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f211,f109])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f210,f114])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f209,f124])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f68,f119])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(f191,plain,
    ( spl9_14
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f163,f122,f107,f189])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f162,f109])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f85,f124])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f187,plain,
    ( spl9_13
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f157,f122,f107,f185])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f156,f109])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f81,f124])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f170,plain,
    ( spl9_11
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f165,f159,f137,f132,f167])).

fof(f165,plain,
    ( r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f164,f134])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))
    | ~ spl9_7
    | ~ spl9_10 ),
    inference(resolution,[],[f160,f139])).

fof(f161,plain,
    ( spl9_10
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f155,f122,f107,f159])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f154,f109])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,a_2_1_lattice3(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f100,f124])).

fof(f100,plain,(
    ! [X2,X3,X1] :
      ( ~ l3_lattices(X1)
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f153,plain,
    ( spl9_9
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f149,f122,f117,f112,f107,f151])).

fof(f149,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f148,f109])).

fof(f148,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f147,f114])).

fof(f147,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f146,f124])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f67,f119])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f145,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f66,f142])).

fof(f66,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k16_lattice3(sK0,sK2)
    & r3_lattice3(sK0,sK1,sK2)
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK0,X2) != X1
              & r3_lattice3(sK0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK0,X2) != X1
            & r3_lattice3(sK0,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k16_lattice3(sK0,X2) != sK1
          & r3_lattice3(sK0,sK1,X2)
          & r2_hidden(sK1,X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k16_lattice3(sK0,X2) != sK1
        & r3_lattice3(sK0,sK1,X2)
        & r2_hidden(sK1,X2) )
   => ( sK1 != k16_lattice3(sK0,sK2)
      & r3_lattice3(sK0,sK1,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(f140,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f65,f137])).

fof(f65,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f135,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f63,f132])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f64,f127])).

fof(f64,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f125,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f62,f122])).

fof(f62,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f61,f117])).

fof(f61,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f60,f112])).

fof(f60,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f59,f107])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28106)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (28106)Refutation not found, incomplete strategy% (28106)------------------------------
% 0.20/0.47  % (28106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (28106)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (28106)Memory used [KB]: 10490
% 0.20/0.47  % (28106)Time elapsed: 0.043 s
% 0.20/0.47  % (28106)------------------------------
% 0.20/0.47  % (28106)------------------------------
% 0.20/0.49  % (28123)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (28110)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (28111)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (28115)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (28111)Refutation not found, incomplete strategy% (28111)------------------------------
% 0.20/0.52  % (28111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28111)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28111)Memory used [KB]: 10490
% 0.20/0.52  % (28111)Time elapsed: 0.095 s
% 0.20/0.52  % (28111)------------------------------
% 0.20/0.52  % (28111)------------------------------
% 0.20/0.52  % (28102)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (28107)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (28107)Refutation not found, incomplete strategy% (28107)------------------------------
% 0.20/0.53  % (28107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28107)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28107)Memory used [KB]: 1663
% 0.20/0.53  % (28107)Time elapsed: 0.082 s
% 0.20/0.53  % (28107)------------------------------
% 0.20/0.53  % (28107)------------------------------
% 0.20/0.53  % (28104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (28103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (28100)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (28105)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (28122)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.49/0.55  % (28119)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.49/0.55  % (28101)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.56  % (28120)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.49/0.56  % (28124)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.49/0.56  % (28100)Refutation not found, incomplete strategy% (28100)------------------------------
% 1.49/0.56  % (28100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (28100)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (28100)Memory used [KB]: 10490
% 1.49/0.56  % (28100)Time elapsed: 0.147 s
% 1.49/0.56  % (28100)------------------------------
% 1.49/0.56  % (28100)------------------------------
% 1.49/0.57  % (28125)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.69/0.57  % (28108)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.69/0.58  % (28118)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.69/0.58  % (28113)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.69/0.58  % (28113)Refutation not found, incomplete strategy% (28113)------------------------------
% 1.69/0.58  % (28113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (28113)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (28113)Memory used [KB]: 6140
% 1.69/0.58  % (28113)Time elapsed: 0.149 s
% 1.69/0.58  % (28113)------------------------------
% 1.69/0.58  % (28113)------------------------------
% 1.69/0.58  % (28114)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.69/0.59  % (28121)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.69/0.59  % (28116)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.69/0.60  % (28117)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.69/0.60  % (28112)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.69/0.61  % (28109)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.91/0.74  % (28109)Refutation not found, incomplete strategy% (28109)------------------------------
% 2.91/0.74  % (28109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.74  % (28109)Termination reason: Refutation not found, incomplete strategy
% 2.91/0.74  
% 2.91/0.74  % (28109)Memory used [KB]: 6012
% 2.91/0.74  % (28109)Time elapsed: 0.314 s
% 2.91/0.74  % (28109)------------------------------
% 2.91/0.74  % (28109)------------------------------
% 4.64/0.94  % (28114)Time limit reached!
% 4.64/0.94  % (28114)------------------------------
% 4.64/0.94  % (28114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/0.94  % (28114)Termination reason: Time limit
% 4.64/0.94  % (28114)Termination phase: Saturation
% 4.64/0.94  
% 4.64/0.94  % (28114)Memory used [KB]: 7931
% 4.64/0.94  % (28114)Time elapsed: 0.525 s
% 4.64/0.94  % (28114)------------------------------
% 4.64/0.94  % (28114)------------------------------
% 4.87/0.99  % (28102)Refutation found. Thanks to Tanya!
% 4.87/0.99  % SZS status Theorem for theBenchmark
% 4.87/1.02  % SZS output start Proof for theBenchmark
% 4.87/1.02  fof(f8659,plain,(
% 4.87/1.02    $false),
% 4.87/1.02    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f153,f161,f170,f187,f191,f216,f223,f235,f255,f259,f267,f279,f283,f292,f307,f321,f348,f381,f385,f405,f476,f606,f678,f735,f875,f1104,f1142,f1411,f1446,f1508,f1512,f1573,f1625,f1659,f1678,f3565,f3881,f3985,f4025,f4236,f4444,f4533,f4593,f4634,f5187,f6850,f6857,f6866,f7116,f8553,f8643,f8658])).
% 4.87/1.02  fof(f8658,plain,(
% 4.87/1.02    spl9_1 | ~spl9_4 | ~spl9_26 | ~spl9_27 | spl9_447 | ~spl9_530),
% 4.87/1.02    inference(avatar_contradiction_clause,[],[f8657])).
% 4.87/1.02  fof(f8657,plain,(
% 4.87/1.02    $false | (spl9_1 | ~spl9_4 | ~spl9_26 | ~spl9_27 | spl9_447 | ~spl9_530)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8656,f109])).
% 4.87/1.02  fof(f109,plain,(
% 4.87/1.02    ~v2_struct_0(sK0) | spl9_1),
% 4.87/1.02    inference(avatar_component_clause,[],[f107])).
% 4.87/1.02  fof(f107,plain,(
% 4.87/1.02    spl9_1 <=> v2_struct_0(sK0)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 4.87/1.02  fof(f8656,plain,(
% 4.87/1.02    v2_struct_0(sK0) | (~spl9_4 | ~spl9_26 | ~spl9_27 | spl9_447 | ~spl9_530)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8655,f124])).
% 4.87/1.02  fof(f124,plain,(
% 4.87/1.02    l3_lattices(sK0) | ~spl9_4),
% 4.87/1.02    inference(avatar_component_clause,[],[f122])).
% 4.87/1.02  fof(f122,plain,(
% 4.87/1.02    spl9_4 <=> l3_lattices(sK0)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 4.87/1.02  fof(f8655,plain,(
% 4.87/1.02    ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl9_26 | ~spl9_27 | spl9_447 | ~spl9_530)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8654,f7115])).
% 4.87/1.02  fof(f7115,plain,(
% 4.87/1.02    ~r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | spl9_447),
% 4.87/1.02    inference(avatar_component_clause,[],[f7113])).
% 4.87/1.02  fof(f7113,plain,(
% 4.87/1.02    spl9_447 <=> r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).
% 4.87/1.02  fof(f8654,plain,(
% 4.87/1.02    r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl9_26 | ~spl9_27 | ~spl9_530)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8653,f290])).
% 4.87/1.02  fof(f290,plain,(
% 4.87/1.02    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl9_27),
% 4.87/1.02    inference(avatar_component_clause,[],[f289])).
% 4.87/1.02  fof(f289,plain,(
% 4.87/1.02    spl9_27 <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 4.87/1.02  fof(f8653,plain,(
% 4.87/1.02    ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl9_26 | ~spl9_530)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8650,f287])).
% 4.87/1.02  fof(f287,plain,(
% 4.87/1.02    r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2)) | ~spl9_26),
% 4.87/1.02    inference(avatar_component_clause,[],[f285])).
% 4.87/1.02  fof(f285,plain,(
% 4.87/1.02    spl9_26 <=> r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 4.87/1.02  fof(f8650,plain,(
% 4.87/1.02    ~r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_530),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f8649])).
% 4.87/1.02  fof(f8649,plain,(
% 4.87/1.02    ~r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_530),
% 4.87/1.02    inference(resolution,[],[f8642,f86])).
% 4.87/1.02  fof(f86,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,sK6(X0,X1,X2)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f50])).
% 4.87/1.02  fof(f50,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 4.87/1.02  fof(f49,plain,(
% 4.87/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 4.87/1.02    introduced(choice_axiom,[])).
% 4.87/1.02  fof(f48,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(rectify,[],[f47])).
% 4.87/1.02  fof(f47,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(nnf_transformation,[],[f24])).
% 4.87/1.02  fof(f24,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(flattening,[],[f23])).
% 4.87/1.02  fof(f23,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.87/1.02    inference(ennf_transformation,[],[f1])).
% 4.87/1.02  fof(f1,axiom,(
% 4.87/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 4.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 4.87/1.02  fof(f8642,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) | ~r2_hidden(X0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_530),
% 4.87/1.02    inference(avatar_component_clause,[],[f8641])).
% 4.87/1.02  fof(f8641,plain,(
% 4.87/1.02    spl9_530 <=> ! [X0] : (r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) | ~r2_hidden(X0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_530])])).
% 4.87/1.02  fof(f8643,plain,(
% 4.87/1.02    spl9_530 | ~spl9_27 | ~spl9_124 | spl9_447 | ~spl9_523),
% 4.87/1.02    inference(avatar_split_clause,[],[f8584,f8550,f7113,f1444,f289,f8641])).
% 4.87/1.02  fof(f1444,plain,(
% 4.87/1.02    spl9_124 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).
% 4.87/1.02  fof(f8550,plain,(
% 4.87/1.02    spl9_523 <=> sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_523])])).
% 4.87/1.02  fof(f8584,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) | ~r2_hidden(X0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_27 | ~spl9_124 | spl9_447 | ~spl9_523)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8583,f7115])).
% 4.87/1.02  fof(f8583,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) | ~r2_hidden(X0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) ) | (~spl9_27 | ~spl9_124 | ~spl9_523)),
% 4.87/1.02    inference(subsumption_resolution,[],[f8569,f290])).
% 4.87/1.02  fof(f8569,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,X0,sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) | ~r2_hidden(X0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) ) | (~spl9_124 | ~spl9_523)),
% 4.87/1.02    inference(superposition,[],[f1445,f8552])).
% 4.87/1.02  fof(f8552,plain,(
% 4.87/1.02    sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2)) | ~spl9_523),
% 4.87/1.02    inference(avatar_component_clause,[],[f8550])).
% 4.87/1.02  fof(f1445,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))) ) | ~spl9_124),
% 4.87/1.02    inference(avatar_component_clause,[],[f1444])).
% 4.87/1.02  fof(f8553,plain,(
% 4.87/1.02    spl9_523 | ~spl9_27 | ~spl9_58 | spl9_447),
% 4.87/1.02    inference(avatar_split_clause,[],[f7125,f7113,f604,f289,f8550])).
% 4.87/1.02  fof(f604,plain,(
% 4.87/1.02    spl9_58 <=> ! [X1,X0] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 4.87/1.02  fof(f7125,plain,(
% 4.87/1.02    sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2)) | (~spl9_27 | ~spl9_58 | spl9_447)),
% 4.87/1.02    inference(subsumption_resolution,[],[f7119,f290])).
% 4.87/1.02  fof(f7119,plain,(
% 4.87/1.02    sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) = sK7(sK6(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),sK0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl9_58 | spl9_447)),
% 4.87/1.02    inference(resolution,[],[f7115,f605])).
% 4.87/1.02  fof(f605,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_58),
% 4.87/1.02    inference(avatar_component_clause,[],[f604])).
% 4.87/1.02  fof(f7116,plain,(
% 4.87/1.02    ~spl9_447 | spl9_24 | ~spl9_27 | ~spl9_344),
% 4.87/1.02    inference(avatar_split_clause,[],[f7100,f5185,f289,f276,f7113])).
% 4.87/1.02  fof(f276,plain,(
% 4.87/1.02    spl9_24 <=> r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 4.87/1.02  fof(f5185,plain,(
% 4.87/1.02    spl9_344 <=> ! [X2] : (r3_lattices(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_344])])).
% 4.87/1.02  fof(f7100,plain,(
% 4.87/1.02    ~r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | (spl9_24 | ~spl9_27 | ~spl9_344)),
% 4.87/1.02    inference(subsumption_resolution,[],[f7076,f278])).
% 4.87/1.02  fof(f278,plain,(
% 4.87/1.02    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | spl9_24),
% 4.87/1.02    inference(avatar_component_clause,[],[f276])).
% 4.87/1.02  fof(f7076,plain,(
% 4.87/1.02    r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | ~r3_lattice3(sK0,sK3(sK0,sK1,sK2),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | (~spl9_27 | ~spl9_344)),
% 4.87/1.02    inference(resolution,[],[f5186,f290])).
% 4.87/1.02  fof(f5186,plain,(
% 4.87/1.02    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattices(sK0,X2,sK1) | ~r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) ) | ~spl9_344),
% 4.87/1.02    inference(avatar_component_clause,[],[f5185])).
% 4.87/1.02  fof(f6866,plain,(
% 4.87/1.02    spl9_1 | ~spl9_4 | ~spl9_6 | spl9_299 | ~spl9_416),
% 4.87/1.02    inference(avatar_contradiction_clause,[],[f6865])).
% 4.87/1.02  fof(f6865,plain,(
% 4.87/1.02    $false | (spl9_1 | ~spl9_4 | ~spl9_6 | spl9_299 | ~spl9_416)),
% 4.87/1.02    inference(subsumption_resolution,[],[f6864,f109])).
% 4.87/1.02  fof(f6864,plain,(
% 4.87/1.02    v2_struct_0(sK0) | (~spl9_4 | ~spl9_6 | spl9_299 | ~spl9_416)),
% 4.87/1.02    inference(subsumption_resolution,[],[f6863,f124])).
% 4.87/1.02  fof(f6863,plain,(
% 4.87/1.02    ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | spl9_299 | ~spl9_416)),
% 4.87/1.02    inference(subsumption_resolution,[],[f6862,f134])).
% 4.87/1.02  fof(f134,plain,(
% 4.87/1.02    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_6),
% 4.87/1.02    inference(avatar_component_clause,[],[f132])).
% 4.87/1.02  fof(f132,plain,(
% 4.87/1.02    spl9_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 4.87/1.02  fof(f6862,plain,(
% 4.87/1.02    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_299 | ~spl9_416)),
% 4.87/1.02    inference(subsumption_resolution,[],[f6860,f4050])).
% 4.87/1.02  fof(f4050,plain,(
% 4.87/1.02    ~r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | spl9_299),
% 4.87/1.02    inference(avatar_component_clause,[],[f4049])).
% 4.87/1.02  fof(f4049,plain,(
% 4.87/1.02    spl9_299 <=> r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).
% 4.87/1.02  fof(f6860,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_416),
% 4.87/1.02    inference(resolution,[],[f6497,f82])).
% 4.87/1.02  fof(f82,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK5(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f46])).
% 4.87/1.02  fof(f46,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 4.87/1.02  fof(f45,plain,(
% 4.87/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 4.87/1.02    introduced(choice_axiom,[])).
% 4.87/1.02  fof(f44,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(rectify,[],[f43])).
% 4.87/1.02  fof(f43,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(nnf_transformation,[],[f22])).
% 4.87/1.02  fof(f22,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(flattening,[],[f21])).
% 4.87/1.02  fof(f21,plain,(
% 4.87/1.02    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.87/1.02    inference(ennf_transformation,[],[f2])).
% 4.87/1.02  fof(f2,axiom,(
% 4.87/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 4.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 4.87/1.02  fof(f6497,plain,(
% 4.87/1.02    r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) | ~spl9_416),
% 4.87/1.02    inference(avatar_component_clause,[],[f6495])).
% 4.87/1.02  fof(f6495,plain,(
% 4.87/1.02    spl9_416 <=> r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_416])])).
% 4.87/1.02  fof(f6857,plain,(
% 4.87/1.02    spl9_416 | ~spl9_5 | ~spl9_6 | ~spl9_441),
% 4.87/1.02    inference(avatar_split_clause,[],[f6855,f6848,f132,f127,f6495])).
% 4.87/1.02  fof(f127,plain,(
% 4.87/1.02    spl9_5 <=> r2_hidden(sK1,sK2)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 4.87/1.02  fof(f6848,plain,(
% 4.87/1.02    spl9_441 <=> ! [X0] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_441])])).
% 4.87/1.02  fof(f6855,plain,(
% 4.87/1.02    r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) | (~spl9_5 | ~spl9_6 | ~spl9_441)),
% 4.87/1.02    inference(subsumption_resolution,[],[f6852,f134])).
% 4.87/1.02  fof(f6852,plain,(
% 4.87/1.02    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) | (~spl9_5 | ~spl9_441)),
% 4.87/1.02    inference(resolution,[],[f6849,f129])).
% 4.87/1.02  fof(f129,plain,(
% 4.87/1.02    r2_hidden(sK1,sK2) | ~spl9_5),
% 4.87/1.02    inference(avatar_component_clause,[],[f127])).
% 4.87/1.02  fof(f6849,plain,(
% 4.87/1.02    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)) ) | ~spl9_441),
% 4.87/1.02    inference(avatar_component_clause,[],[f6848])).
% 4.87/1.02  fof(f6850,plain,(
% 4.87/1.02    spl9_441 | ~spl9_6 | ~spl9_119 | ~spl9_295 | spl9_299),
% 4.87/1.02    inference(avatar_split_clause,[],[f6842,f4049,f4018,f1409,f132,f6848])).
% 4.87/1.02  fof(f1409,plain,(
% 4.87/1.02    spl9_119 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).
% 4.87/1.02  fof(f4018,plain,(
% 4.87/1.02    spl9_295 <=> sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_295])])).
% 4.87/1.02  fof(f6842,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) ) | (~spl9_6 | ~spl9_119 | ~spl9_295 | spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4039,f4050])).
% 4.87/1.02  fof(f4039,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))) ) | (~spl9_6 | ~spl9_119 | ~spl9_295)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4031,f134])).
% 4.87/1.02  fof(f4031,plain,(
% 4.87/1.02    ( ! [X0] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))) ) | (~spl9_119 | ~spl9_295)),
% 4.87/1.02    inference(superposition,[],[f1410,f4020])).
% 4.87/1.02  fof(f4020,plain,(
% 4.87/1.02    sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2) | ~spl9_295),
% 4.87/1.02    inference(avatar_component_clause,[],[f4018])).
% 4.87/1.02  fof(f1410,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_119),
% 4.87/1.02    inference(avatar_component_clause,[],[f1409])).
% 4.87/1.02  fof(f5187,plain,(
% 4.87/1.02    spl9_344 | ~spl9_17 | ~spl9_318),
% 4.87/1.02    inference(avatar_split_clause,[],[f4659,f4437,f221,f5185])).
% 4.87/1.02  fof(f221,plain,(
% 4.87/1.02    spl9_17 <=> ! [X1,X0] : (r3_lattices(sK0,X1,k15_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 4.87/1.02  fof(f4437,plain,(
% 4.87/1.02    spl9_318 <=> sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_318])])).
% 4.87/1.02  fof(f4659,plain,(
% 4.87/1.02    ( ! [X2] : (r3_lattices(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))) ) | (~spl9_17 | ~spl9_318)),
% 4.87/1.02    inference(superposition,[],[f222,f4439])).
% 4.87/1.02  fof(f4439,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~spl9_318),
% 4.87/1.02    inference(avatar_component_clause,[],[f4437])).
% 4.87/1.02  fof(f222,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattices(sK0,X1,k15_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0))) ) | ~spl9_17),
% 4.87/1.02    inference(avatar_component_clause,[],[f221])).
% 4.87/1.02  fof(f4634,plain,(
% 4.87/1.02    spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_11 | spl9_319 | ~spl9_322 | ~spl9_324),
% 4.87/1.02    inference(avatar_contradiction_clause,[],[f4629])).
% 4.87/1.02  fof(f4629,plain,(
% 4.87/1.02    $false | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_11 | spl9_319 | ~spl9_322 | ~spl9_324)),
% 4.87/1.02    inference(unit_resulting_resolution,[],[f109,f124,f134,f169,f4443,f4475,f4592,f79])).
% 4.87/1.02  fof(f79,plain,(
% 4.87/1.02    ( ! [X4,X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f46])).
% 4.87/1.02  fof(f4592,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | ~spl9_324),
% 4.87/1.02    inference(avatar_component_clause,[],[f4590])).
% 4.87/1.02  fof(f4590,plain,(
% 4.87/1.02    spl9_324 <=> r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_324])])).
% 4.87/1.02  fof(f4475,plain,(
% 4.87/1.02    m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~spl9_322),
% 4.87/1.02    inference(avatar_component_clause,[],[f4474])).
% 4.87/1.02  fof(f4474,plain,(
% 4.87/1.02    spl9_322 <=> m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).
% 4.87/1.02  fof(f4443,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | spl9_319),
% 4.87/1.02    inference(avatar_component_clause,[],[f4441])).
% 4.87/1.02  fof(f4441,plain,(
% 4.87/1.02    spl9_319 <=> r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).
% 4.87/1.02  fof(f169,plain,(
% 4.87/1.02    r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) | ~spl9_11),
% 4.87/1.02    inference(avatar_component_clause,[],[f167])).
% 4.87/1.02  fof(f167,plain,(
% 4.87/1.02    spl9_11 <=> r2_hidden(sK1,a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 4.87/1.02  fof(f4593,plain,(
% 4.87/1.02    spl9_318 | spl9_324 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299),
% 4.87/1.02    inference(avatar_split_clause,[],[f4347,f4049,f132,f122,f117,f112,f107,f4590,f4437])).
% 4.87/1.02  fof(f112,plain,(
% 4.87/1.02    spl9_2 <=> v10_lattices(sK0)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 4.87/1.02  fof(f117,plain,(
% 4.87/1.02    spl9_3 <=> v4_lattice3(sK0)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 4.87/1.02  fof(f4347,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4346,f109])).
% 4.87/1.02  fof(f4346,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4345,f114])).
% 4.87/1.02  fof(f114,plain,(
% 4.87/1.02    v10_lattices(sK0) | ~spl9_2),
% 4.87/1.02    inference(avatar_component_clause,[],[f112])).
% 4.87/1.02  fof(f4345,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4344,f119])).
% 4.87/1.02  fof(f119,plain,(
% 4.87/1.02    v4_lattice3(sK0) | ~spl9_3),
% 4.87/1.02    inference(avatar_component_clause,[],[f117])).
% 4.87/1.02  fof(f4344,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4343,f124])).
% 4.87/1.02  fof(f4343,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4335,f134])).
% 4.87/1.02  fof(f4335,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),a_2_1_lattice3(sK0,sK2)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_299),
% 4.87/1.02    inference(resolution,[],[f4051,f104])).
% 4.87/1.02  fof(f104,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X2,X1) | r4_lattice3(X0,sK4(X0,X1,X2),X1) | k15_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f77])).
% 4.87/1.02  fof(f77,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK4(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f42])).
% 4.87/1.02  fof(f42,plain,(
% 4.87/1.02    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 4.87/1.02  fof(f41,plain,(
% 4.87/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 4.87/1.02    introduced(choice_axiom,[])).
% 4.87/1.02  fof(f40,plain,(
% 4.87/1.02    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(rectify,[],[f39])).
% 4.87/1.02  fof(f39,plain,(
% 4.87/1.02    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(flattening,[],[f38])).
% 4.87/1.02  fof(f38,plain,(
% 4.87/1.02    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(nnf_transformation,[],[f20])).
% 4.87/1.02  fof(f20,plain,(
% 4.87/1.02    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.87/1.02    inference(flattening,[],[f19])).
% 4.87/1.02  fof(f19,plain,(
% 4.87/1.02    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.87/1.02    inference(ennf_transformation,[],[f3])).
% 4.87/1.02  fof(f3,axiom,(
% 4.87/1.02    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 4.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 4.87/1.02  fof(f4051,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~spl9_299),
% 4.87/1.02    inference(avatar_component_clause,[],[f4049])).
% 4.87/1.02  fof(f4533,plain,(
% 4.87/1.02    spl9_318 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299 | spl9_322),
% 4.87/1.02    inference(avatar_split_clause,[],[f4512,f4474,f4049,f132,f122,f117,f112,f107,f4437])).
% 4.87/1.02  fof(f4512,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4511,f109])).
% 4.87/1.02  fof(f4511,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4510,f114])).
% 4.87/1.02  fof(f4510,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4509,f119])).
% 4.87/1.02  fof(f4509,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_6 | ~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4508,f124])).
% 4.87/1.02  fof(f4508,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4507,f134])).
% 4.87/1.02  fof(f4507,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_299 | spl9_322)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4506,f4051])).
% 4.87/1.02  fof(f4506,plain,(
% 4.87/1.02    sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | spl9_322),
% 4.87/1.02    inference(resolution,[],[f4476,f103])).
% 4.87/1.02  fof(f103,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | k15_lattice3(X0,X1) = X2 | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f76])).
% 4.87/1.02  fof(f76,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f42])).
% 4.87/1.02  fof(f4476,plain,(
% 4.87/1.02    ~m1_subset_1(sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl9_322),
% 4.87/1.02    inference(avatar_component_clause,[],[f4474])).
% 4.87/1.02  fof(f4444,plain,(
% 4.87/1.02    spl9_318 | ~spl9_319 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299),
% 4.87/1.02    inference(avatar_split_clause,[],[f4342,f4049,f132,f122,f117,f112,f107,f4441,f4437])).
% 4.87/1.02  fof(f4342,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4341,f109])).
% 4.87/1.02  fof(f4341,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4340,f114])).
% 4.87/1.02  fof(f4340,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4339,f119])).
% 4.87/1.02  fof(f4339,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4338,f124])).
% 4.87/1.02  fof(f4338,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4334,f134])).
% 4.87/1.02  fof(f4334,plain,(
% 4.87/1.02    ~r1_lattices(sK0,sK1,sK4(sK0,a_2_1_lattice3(sK0,sK2),sK1)) | sK1 = k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_299),
% 4.87/1.02    inference(resolution,[],[f4051,f105])).
% 4.87/1.02  fof(f105,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X2,X1) | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | k15_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f78])).
% 4.87/1.02  fof(f78,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f42])).
% 4.87/1.02  fof(f4236,plain,(
% 4.87/1.02    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_139 | ~spl9_296 | spl9_299),
% 4.87/1.02    inference(avatar_contradiction_clause,[],[f4235])).
% 4.87/1.02  fof(f4235,plain,(
% 4.87/1.02    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_139 | ~spl9_296 | spl9_299)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4116,f4050])).
% 4.87/1.02  fof(f4116,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_139 | ~spl9_296)),
% 4.87/1.02    inference(forward_demodulation,[],[f4115,f1677])).
% 4.87/1.02  fof(f1677,plain,(
% 4.87/1.02    sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)) | ~spl9_139),
% 4.87/1.02    inference(avatar_component_clause,[],[f1675])).
% 4.87/1.02  fof(f1675,plain,(
% 4.87/1.02    spl9_139 <=> sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).
% 4.87/1.02  fof(f4115,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_296)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4114,f109])).
% 4.87/1.02  fof(f4114,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_296)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4113,f114])).
% 4.87/1.02  fof(f4113,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_296)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4112,f119])).
% 4.87/1.02  fof(f4112,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_296)),
% 4.87/1.02    inference(subsumption_resolution,[],[f4100,f124])).
% 4.87/1.02  fof(f4100,plain,(
% 4.87/1.02    r4_lattice3(sK0,sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_296),
% 4.87/1.02    inference(resolution,[],[f4024,f89])).
% 4.87/1.02  fof(f89,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | r4_lattice3(X1,sK7(X0,X1,X2),X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f54])).
% 4.87/1.02  fof(f54,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK7(X0,X1,X2),X2) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).
% 4.87/1.02  fof(f53,plain,(
% 4.87/1.02    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK7(X0,X1,X2),X2) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 4.87/1.02    introduced(choice_axiom,[])).
% 4.87/1.02  fof(f52,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(rectify,[],[f51])).
% 4.87/1.02  fof(f51,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(nnf_transformation,[],[f26])).
% 4.87/1.02  fof(f26,plain,(
% 4.87/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(flattening,[],[f25])).
% 4.87/1.02  fof(f25,plain,(
% 4.87/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 4.87/1.02    inference(ennf_transformation,[],[f5])).
% 4.87/1.02  fof(f5,axiom,(
% 4.87/1.02    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 4.87/1.02  fof(f4024,plain,(
% 4.87/1.02    r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | ~spl9_296),
% 4.87/1.02    inference(avatar_component_clause,[],[f4022])).
% 4.87/1.02  fof(f4022,plain,(
% 4.87/1.02    spl9_296 <=> r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_296])])).
% 4.87/1.02  fof(f4025,plain,(
% 4.87/1.02    spl9_295 | spl9_296 | ~spl9_139 | ~spl9_293),
% 4.87/1.02    inference(avatar_split_clause,[],[f3999,f3983,f1675,f4022,f4018])).
% 4.87/1.02  fof(f3983,plain,(
% 4.87/1.02    spl9_293 <=> ! [X1] : (r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).
% 4.87/1.02  fof(f3999,plain,(
% 4.87/1.02    r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) | sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2) | (~spl9_139 | ~spl9_293)),
% 4.87/1.02    inference(superposition,[],[f3984,f1677])).
% 4.87/1.02  fof(f3984,plain,(
% 4.87/1.02    ( ! [X1] : (r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1)) ) | ~spl9_293),
% 4.87/1.02    inference(avatar_component_clause,[],[f3983])).
% 4.87/1.02  fof(f3985,plain,(
% 4.87/1.02    spl9_293 | ~spl9_6 | ~spl9_290),
% 4.87/1.02    inference(avatar_split_clause,[],[f3941,f3879,f132,f3983])).
% 4.87/1.02  fof(f3879,plain,(
% 4.87/1.02    spl9_290 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_290])])).
% 4.87/1.02  fof(f3941,plain,(
% 4.87/1.02    ( ! [X1] : (r2_hidden(sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1)) ) | (~spl9_6 | ~spl9_290)),
% 4.87/1.02    inference(resolution,[],[f3880,f134])).
% 4.87/1.02  fof(f3880,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)) ) | ~spl9_290),
% 4.87/1.02    inference(avatar_component_clause,[],[f3879])).
% 4.87/1.02  fof(f3881,plain,(
% 4.87/1.02    spl9_290 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59 | ~spl9_280),
% 4.87/1.02    inference(avatar_split_clause,[],[f3849,f3563,f676,f122,f117,f112,f107,f3879])).
% 4.87/1.02  fof(f676,plain,(
% 4.87/1.02    spl9_59 <=> ! [X7,X8] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 4.87/1.02  fof(f3563,plain,(
% 4.87/1.02    spl9_280 <=> ! [X7,X8] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).
% 4.87/1.02  fof(f3849,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59 | ~spl9_280)),
% 4.87/1.02    inference(subsumption_resolution,[],[f3848,f677])).
% 4.87/1.02  fof(f677,plain,(
% 4.87/1.02    ( ! [X8,X7] : (r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)) ) | ~spl9_59),
% 4.87/1.02    inference(avatar_component_clause,[],[f676])).
% 4.87/1.02  fof(f3848,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_280)),
% 4.87/1.02    inference(subsumption_resolution,[],[f3847,f109])).
% 4.87/1.02  fof(f3847,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_280)),
% 4.87/1.02    inference(subsumption_resolution,[],[f3846,f114])).
% 4.87/1.02  fof(f3846,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_280)),
% 4.87/1.02    inference(subsumption_resolution,[],[f3845,f119])).
% 4.87/1.02  fof(f3845,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_280)),
% 4.87/1.02    inference(subsumption_resolution,[],[f3816,f124])).
% 4.87/1.02  fof(f3816,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X1))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_280),
% 4.87/1.02    inference(resolution,[],[f3564,f87])).
% 4.87/1.02  fof(f87,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f54])).
% 4.87/1.02  fof(f3564,plain,(
% 4.87/1.02    ( ! [X8,X7] : (~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8)) ) | ~spl9_280),
% 4.87/1.02    inference(avatar_component_clause,[],[f3563])).
% 4.87/1.02  fof(f3565,plain,(
% 4.87/1.02    spl9_280 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_128),
% 4.87/1.02    inference(avatar_split_clause,[],[f1569,f1510,f122,f117,f112,f107,f3563])).
% 4.87/1.02  fof(f1510,plain,(
% 4.87/1.02    spl9_128 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).
% 4.87/1.02  fof(f1569,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_128)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1568,f109])).
% 4.87/1.02  fof(f1568,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_128)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1567,f114])).
% 4.87/1.02  fof(f1567,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_128)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1566,f119])).
% 4.87/1.02  fof(f1566,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_128)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1553,f124])).
% 4.87/1.02  fof(f1553,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(sK7(X7,sK0,a_2_1_lattice3(sK0,X8)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_128),
% 4.87/1.02    inference(resolution,[],[f1511,f99])).
% 4.87/1.02  fof(f99,plain,(
% 4.87/1.02    ( ! [X2,X3,X1] : (~r4_lattice3(X1,X3,X2) | r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(equality_resolution,[],[f90])).
% 4.87/1.02  fof(f90,plain,(
% 4.87/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f54])).
% 4.87/1.02  fof(f1511,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_128),
% 4.87/1.02    inference(avatar_component_clause,[],[f1510])).
% 4.87/1.02  fof(f1678,plain,(
% 4.87/1.02    spl9_139 | ~spl9_5 | ~spl9_137),
% 4.87/1.02    inference(avatar_split_clause,[],[f1660,f1657,f127,f1675])).
% 4.87/1.02  fof(f1657,plain,(
% 4.87/1.02    spl9_137 <=> ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).
% 4.87/1.02  fof(f1660,plain,(
% 4.87/1.02    sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,sK2)) | (~spl9_5 | ~spl9_137)),
% 4.87/1.02    inference(resolution,[],[f1658,f129])).
% 4.87/1.02  fof(f1658,plain,(
% 4.87/1.02    ( ! [X5] : (~r2_hidden(sK1,X5) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5))) ) | ~spl9_137),
% 4.87/1.02    inference(avatar_component_clause,[],[f1657])).
% 4.87/1.02  fof(f1659,plain,(
% 4.87/1.02    spl9_137 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_136),
% 4.87/1.02    inference(avatar_split_clause,[],[f1648,f1623,f122,f117,f112,f107,f1657])).
% 4.87/1.02  fof(f1623,plain,(
% 4.87/1.02    spl9_136 <=> ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 4.87/1.02  fof(f1648,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_136)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1647,f109])).
% 4.87/1.02  fof(f1647,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_136)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1646,f114])).
% 4.87/1.02  fof(f1646,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_136)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1645,f119])).
% 4.87/1.02  fof(f1645,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_136)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1638,f124])).
% 4.87/1.02  fof(f1638,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_136),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f1637])).
% 4.87/1.02  fof(f1637,plain,(
% 4.87/1.02    ( ! [X5] : (sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~r2_hidden(sK1,X5) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X5)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_136),
% 4.87/1.02    inference(resolution,[],[f1624,f88])).
% 4.87/1.02  fof(f88,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sK7(X0,X1,X2) = X0 | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f54])).
% 4.87/1.02  fof(f1624,plain,(
% 4.87/1.02    ( ! [X4] : (r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | ~r2_hidden(sK1,X4)) ) | ~spl9_136),
% 4.87/1.02    inference(avatar_component_clause,[],[f1623])).
% 4.87/1.02  fof(f1625,plain,(
% 4.87/1.02    spl9_136 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_135),
% 4.87/1.02    inference(avatar_split_clause,[],[f1601,f1571,f132,f122,f117,f112,f107,f1623])).
% 4.87/1.02  fof(f1571,plain,(
% 4.87/1.02    spl9_135 <=> ! [X4] : (~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).
% 4.87/1.02  fof(f1601,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_135)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1600,f109])).
% 4.87/1.02  fof(f1600,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_135)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1599,f114])).
% 4.87/1.02  fof(f1599,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_135)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1598,f119])).
% 4.87/1.02  fof(f1598,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_6 | ~spl9_135)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1597,f124])).
% 4.87/1.02  fof(f1597,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_6 | ~spl9_135)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1583,f134])).
% 4.87/1.02  fof(f1583,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r2_hidden(sK1,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X4))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_135),
% 4.87/1.02    inference(resolution,[],[f1572,f99])).
% 4.87/1.02  fof(f1572,plain,(
% 4.87/1.02    ( ! [X4] : (r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | ~r2_hidden(sK1,X4) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))) ) | ~spl9_135),
% 4.87/1.02    inference(avatar_component_clause,[],[f1571])).
% 4.87/1.02  fof(f1573,plain,(
% 4.87/1.02    spl9_135 | spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_127),
% 4.87/1.02    inference(avatar_split_clause,[],[f1546,f1506,f132,f122,f107,f1571])).
% 4.87/1.02  fof(f1506,plain,(
% 4.87/1.02    spl9_127 <=> ! [X1,X0] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).
% 4.87/1.02  fof(f1546,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_127)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1545,f109])).
% 4.87/1.02  fof(f1545,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_6 | ~spl9_127)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1544,f124])).
% 4.87/1.02  fof(f1544,plain,(
% 4.87/1.02    ( ! [X4] : (~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_6 | ~spl9_127)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1541,f134])).
% 4.87/1.02  fof(f1541,plain,(
% 4.87/1.02    ( ! [X4] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_127),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f1539])).
% 4.87/1.02  fof(f1539,plain,(
% 4.87/1.02    ( ! [X4] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,X4) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X4)) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X4)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_127),
% 4.87/1.02    inference(resolution,[],[f1507,f82])).
% 4.87/1.02  fof(f1507,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0))) ) | ~spl9_127),
% 4.87/1.02    inference(avatar_component_clause,[],[f1506])).
% 4.87/1.02  fof(f1512,plain,(
% 4.87/1.02    spl9_128 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59),
% 4.87/1.02    inference(avatar_split_clause,[],[f696,f676,f122,f117,f112,f107,f1510])).
% 4.87/1.02  fof(f696,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f695,f109])).
% 4.87/1.02  fof(f695,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f694,f114])).
% 4.87/1.02  fof(f694,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f693,f119])).
% 4.87/1.02  fof(f693,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f691,f124])).
% 4.87/1.02  fof(f691,plain,(
% 4.87/1.02    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | r4_lattice3(sK0,sK7(X0,sK0,a_2_1_lattice3(sK0,X1)),a_2_1_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_59),
% 4.87/1.02    inference(resolution,[],[f677,f89])).
% 4.87/1.02  fof(f1508,plain,(
% 4.87/1.02    spl9_127 | ~spl9_6 | ~spl9_80 | ~spl9_119),
% 4.87/1.02    inference(avatar_split_clause,[],[f1471,f1409,f873,f132,f1506])).
% 4.87/1.02  fof(f873,plain,(
% 4.87/1.02    spl9_80 <=> ! [X1] : (sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).
% 4.87/1.02  fof(f1471,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0))) ) | (~spl9_6 | ~spl9_80 | ~spl9_119)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1468,f134])).
% 4.87/1.02  fof(f1468,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,X0)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,X0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X0))) ) | (~spl9_80 | ~spl9_119)),
% 4.87/1.02    inference(superposition,[],[f1410,f874])).
% 4.87/1.02  fof(f874,plain,(
% 4.87/1.02    ( ! [X1] : (sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1))) ) | ~spl9_80),
% 4.87/1.02    inference(avatar_component_clause,[],[f873])).
% 4.87/1.02  fof(f1446,plain,(
% 4.87/1.02    spl9_124 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_14 | ~spl9_101),
% 4.87/1.02    inference(avatar_split_clause,[],[f1200,f1140,f189,f122,f117,f112,f107,f1444])).
% 4.87/1.02  fof(f189,plain,(
% 4.87/1.02    spl9_14 <=> ! [X1,X0] : (r2_hidden(sK6(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 4.87/1.02  fof(f1140,plain,(
% 4.87/1.02    spl9_101 <=> ! [X5,X4,X6] : (r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5)) | ~m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).
% 4.87/1.02  fof(f1200,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_14 | ~spl9_101)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1199,f190])).
% 4.87/1.02  fof(f190,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1)) ) | ~spl9_14),
% 4.87/1.02    inference(avatar_component_clause,[],[f189])).
% 4.87/1.02  fof(f1199,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_101)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1198,f109])).
% 4.87/1.02  fof(f1198,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_101)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1197,f114])).
% 4.87/1.02  fof(f1197,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_101)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1196,f119])).
% 4.87/1.02  fof(f1196,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_101)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1195,f124])).
% 4.87/1.02  fof(f1195,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),sK0,X2)) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK6(sK0,X0,a_2_2_lattice3(sK0,X2)),a_2_2_lattice3(sK0,X2)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_101),
% 4.87/1.02    inference(resolution,[],[f1141,f87])).
% 4.87/1.02  fof(f1141,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (~m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5)) | r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5))) ) | ~spl9_101),
% 4.87/1.02    inference(avatar_component_clause,[],[f1140])).
% 4.87/1.02  fof(f1411,plain,(
% 4.87/1.02    spl9_119 | spl9_1 | ~spl9_4 | ~spl9_13 | ~spl9_97),
% 4.87/1.02    inference(avatar_split_clause,[],[f1151,f1102,f185,f122,f107,f1409])).
% 4.87/1.02  fof(f185,plain,(
% 4.87/1.02    spl9_13 <=> ! [X1,X0] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 4.87/1.02  fof(f1102,plain,(
% 4.87/1.02    spl9_97 <=> ! [X5,X4,X6] : (r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).
% 4.87/1.02  fof(f1151,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1)) ) | (spl9_1 | ~spl9_4 | ~spl9_13 | ~spl9_97)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1150,f186])).
% 4.87/1.02  fof(f186,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | ~spl9_13),
% 4.87/1.02    inference(avatar_component_clause,[],[f185])).
% 4.87/1.02  fof(f1150,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) | ~r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2))) ) | (spl9_1 | ~spl9_4 | ~spl9_97)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1149,f109])).
% 4.87/1.02  fof(f1149,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) | ~r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2)) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_97)),
% 4.87/1.02    inference(subsumption_resolution,[],[f1147,f124])).
% 4.87/1.02  fof(f1147,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X2)) | r1_lattices(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),sK0,X2),X1) | ~r2_hidden(sK5(sK0,X0,a_2_1_lattice3(sK0,X2)),a_2_1_lattice3(sK0,X2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_97),
% 4.87/1.02    inference(resolution,[],[f1103,f91])).
% 4.87/1.02  fof(f91,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 4.87/1.02    inference(cnf_transformation,[],[f58])).
% 4.87/1.02  fof(f58,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK8(X0,X1,X2),X2) & sK8(X0,X1,X2) = X0 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).
% 4.87/1.02  fof(f57,plain,(
% 4.87/1.02    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK8(X0,X1,X2),X2) & sK8(X0,X1,X2) = X0 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 4.87/1.02    introduced(choice_axiom,[])).
% 4.87/1.02  fof(f56,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(rectify,[],[f55])).
% 4.87/1.02  fof(f55,plain,(
% 4.87/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(nnf_transformation,[],[f28])).
% 4.87/1.02  fof(f28,plain,(
% 4.87/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 4.87/1.02    inference(flattening,[],[f27])).
% 4.87/1.02  fof(f27,plain,(
% 4.87/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 4.87/1.02    inference(ennf_transformation,[],[f4])).
% 4.87/1.02  fof(f4,axiom,(
% 4.87/1.02    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 4.87/1.02  fof(f1103,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (~m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5)) | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6)) ) | ~spl9_97),
% 4.87/1.02    inference(avatar_component_clause,[],[f1102])).
% 4.87/1.02  fof(f1142,plain,(
% 4.87/1.02    spl9_101 | spl9_1 | ~spl9_4 | ~spl9_41),
% 4.87/1.02    inference(avatar_split_clause,[],[f445,f403,f122,f107,f1140])).
% 4.87/1.02  fof(f403,plain,(
% 4.87/1.02    spl9_41 <=> ! [X1,X0] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 4.87/1.02  fof(f445,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5)) | ~m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_41)),
% 4.87/1.02    inference(subsumption_resolution,[],[f444,f109])).
% 4.87/1.02  fof(f444,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5)) | ~m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_41)),
% 4.87/1.02    inference(subsumption_resolution,[],[f434,f124])).
% 4.87/1.02  fof(f434,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (r3_lattice3(sK0,X4,a_2_2_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_lattices(sK0,X6,sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5)) | ~m1_subset_1(sK7(sK6(sK0,X4,a_2_2_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_41),
% 4.87/1.02    inference(resolution,[],[f404,f79])).
% 4.87/1.02  fof(f404,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_41),
% 4.87/1.02    inference(avatar_component_clause,[],[f403])).
% 4.87/1.02  fof(f1104,plain,(
% 4.87/1.02    spl9_97 | ~spl9_18 | ~spl9_37),
% 4.87/1.02    inference(avatar_split_clause,[],[f408,f379,f233,f1102])).
% 4.87/1.02  fof(f233,plain,(
% 4.87/1.02    spl9_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X0))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 4.87/1.02  fof(f379,plain,(
% 4.87/1.02    spl9_37 <=> ! [X1,X0] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 4.87/1.02  fof(f408,plain,(
% 4.87/1.02    ( ! [X6,X4,X5] : (r4_lattice3(sK0,X4,a_2_1_lattice3(sK0,X5)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,X5) | ~m1_subset_1(sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),u1_struct_0(sK0)) | r1_lattices(sK0,sK8(sK5(sK0,X4,a_2_1_lattice3(sK0,X5)),sK0,X5),X6)) ) | (~spl9_18 | ~spl9_37)),
% 4.87/1.02    inference(resolution,[],[f380,f234])).
% 4.87/1.02  fof(f234,plain,(
% 4.87/1.02    ( ! [X2,X0,X1] : (~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X0)) ) | ~spl9_18),
% 4.87/1.02    inference(avatar_component_clause,[],[f233])).
% 4.87/1.02  fof(f380,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_37),
% 4.87/1.02    inference(avatar_component_clause,[],[f379])).
% 4.87/1.02  fof(f875,plain,(
% 4.87/1.02    spl9_80 | ~spl9_6 | ~spl9_64),
% 4.87/1.02    inference(avatar_split_clause,[],[f843,f733,f132,f873])).
% 4.87/1.02  fof(f733,plain,(
% 4.87/1.02    spl9_64 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2)),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 4.87/1.02  fof(f843,plain,(
% 4.87/1.02    ( ! [X1] : (sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,sK1,a_2_1_lattice3(sK0,X1)),sK0,X1) | sK1 = sK7(sK1,sK0,a_2_1_lattice3(sK0,X1))) ) | (~spl9_6 | ~spl9_64)),
% 4.87/1.02    inference(resolution,[],[f734,f134])).
% 4.87/1.02  fof(f734,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2) ) | ~spl9_64),
% 4.87/1.02    inference(avatar_component_clause,[],[f733])).
% 4.87/1.02  fof(f735,plain,(
% 4.87/1.02    spl9_64 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59),
% 4.87/1.02    inference(avatar_split_clause,[],[f700,f676,f122,f117,f112,f107,f733])).
% 4.87/1.02  fof(f700,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f699,f109])).
% 4.87/1.02  fof(f699,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f698,f114])).
% 4.87/1.02  fof(f698,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f697,f119])).
% 4.87/1.02  fof(f697,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_59)),
% 4.87/1.02    inference(subsumption_resolution,[],[f692,f124])).
% 4.87/1.02  fof(f692,plain,(
% 4.87/1.02    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK5(sK0,X2,a_2_1_lattice3(sK0,X3)) = sK8(sK5(sK0,X2,a_2_1_lattice3(sK0,X3)),sK0,X3) | sK7(X2,sK0,a_2_1_lattice3(sK0,X3)) = X2 | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_59),
% 4.87/1.02    inference(resolution,[],[f677,f88])).
% 4.87/1.02  fof(f678,plain,(
% 4.87/1.02    spl9_59 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_46),
% 4.87/1.02    inference(avatar_split_clause,[],[f631,f474,f122,f117,f112,f107,f676])).
% 4.87/1.02  fof(f474,plain,(
% 4.87/1.02    spl9_46 <=> ! [X1,X0] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 4.87/1.02  fof(f631,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_46)),
% 4.87/1.02    inference(subsumption_resolution,[],[f630,f109])).
% 4.87/1.02  fof(f630,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_46)),
% 4.87/1.02    inference(subsumption_resolution,[],[f629,f114])).
% 4.87/1.02  fof(f629,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_46)),
% 4.87/1.02    inference(subsumption_resolution,[],[f628,f119])).
% 4.87/1.02  fof(f628,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_46)),
% 4.87/1.02    inference(subsumption_resolution,[],[f614,f124])).
% 4.87/1.02  fof(f614,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_46),
% 4.87/1.02    inference(duplicate_literal_removal,[],[f613])).
% 4.87/1.02  fof(f613,plain,(
% 4.87/1.02    ( ! [X8,X7] : (sK5(sK0,X7,a_2_1_lattice3(sK0,X8)) = sK8(sK5(sK0,X7,a_2_1_lattice3(sK0,X8)),sK0,X8) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_2_lattice3(sK0,a_2_1_lattice3(sK0,X8))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_46),
% 4.87/1.02    inference(resolution,[],[f475,f99])).
% 4.87/1.02  fof(f475,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl9_46),
% 4.87/1.02    inference(avatar_component_clause,[],[f474])).
% 4.87/1.02  fof(f606,plain,(
% 4.87/1.02    spl9_58 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_38),
% 4.87/1.02    inference(avatar_split_clause,[],[f401,f383,f122,f117,f112,f107,f604])).
% 4.87/1.02  fof(f383,plain,(
% 4.87/1.02    spl9_38 <=> ! [X9,X11,X10] : (~m1_subset_1(X9,u1_struct_0(sK0)) | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11)) | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 4.87/1.02  fof(f401,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_38)),
% 4.87/1.02    inference(subsumption_resolution,[],[f400,f109])).
% 4.87/1.02  fof(f400,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_38)),
% 4.87/1.02    inference(subsumption_resolution,[],[f399,f114])).
% 4.87/1.02  fof(f399,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_38)),
% 4.87/1.02    inference(subsumption_resolution,[],[f398,f124])).
% 4.87/1.02  fof(f398,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | sK6(sK0,X0,a_2_2_lattice3(sK0,X1)) = sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_38)),
% 4.87/1.02    inference(resolution,[],[f384,f119])).
% 4.87/1.02  fof(f384,plain,(
% 4.87/1.02    ( ! [X10,X11,X9] : (~v4_lattice3(X10) | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11)) | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11) | ~l3_lattices(X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~v10_lattices(X10) | v2_struct_0(X10)) ) | ~spl9_38),
% 4.87/1.02    inference(avatar_component_clause,[],[f383])).
% 4.87/1.02  fof(f476,plain,(
% 4.87/1.02    spl9_46 | spl9_1 | ~spl9_4 | ~spl9_29),
% 4.87/1.02    inference(avatar_split_clause,[],[f351,f319,f122,f107,f474])).
% 4.87/1.02  fof(f319,plain,(
% 4.87/1.02    spl9_29 <=> ! [X3,X5,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5)) | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5) | ~l3_lattices(X4) | v2_struct_0(X4))),
% 4.87/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 4.87/1.02  fof(f351,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_29)),
% 4.87/1.02    inference(subsumption_resolution,[],[f350,f109])).
% 4.87/1.02  fof(f350,plain,(
% 4.87/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_29)),
% 4.87/1.02    inference(resolution,[],[f320,f124])).
% 4.87/1.02  fof(f320,plain,(
% 4.87/1.02    ( ! [X4,X5,X3] : (~l3_lattices(X4) | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5)) | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(X4)) ) | ~spl9_29),
% 4.87/1.02    inference(avatar_component_clause,[],[f319])).
% 5.30/1.02  fof(f405,plain,(
% 5.30/1.02    spl9_41 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_34),
% 5.30/1.02    inference(avatar_split_clause,[],[f370,f346,f122,f117,f112,f107,f403])).
% 5.30/1.02  fof(f346,plain,(
% 5.30/1.02    spl9_34 <=> ! [X7,X8,X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8)) | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8) | ~l3_lattices(X7) | ~v4_lattice3(X7) | ~v10_lattices(X7) | v2_struct_0(X7))),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 5.30/1.02  fof(f370,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_34)),
% 5.30/1.02    inference(subsumption_resolution,[],[f369,f109])).
% 5.30/1.02  fof(f369,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_34)),
% 5.30/1.02    inference(subsumption_resolution,[],[f368,f114])).
% 5.30/1.02  fof(f368,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4 | ~spl9_34)),
% 5.30/1.02    inference(subsumption_resolution,[],[f367,f124])).
% 5.30/1.02  fof(f367,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r3_lattice3(sK0,X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(sK6(sK0,X0,a_2_2_lattice3(sK0,X1)),sK0,X1),X1) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_34)),
% 5.30/1.02    inference(resolution,[],[f347,f119])).
% 5.30/1.02  fof(f347,plain,(
% 5.30/1.02    ( ! [X6,X8,X7] : (~v4_lattice3(X7) | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8)) | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8) | ~l3_lattices(X7) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v10_lattices(X7) | v2_struct_0(X7)) ) | ~spl9_34),
% 5.30/1.02    inference(avatar_component_clause,[],[f346])).
% 5.30/1.02  fof(f385,plain,(
% 5.30/1.02    spl9_38 | ~spl9_14),
% 5.30/1.02    inference(avatar_split_clause,[],[f204,f189,f383])).
% 5.30/1.02  fof(f204,plain,(
% 5.30/1.02    ( ! [X10,X11,X9] : (~m1_subset_1(X9,u1_struct_0(sK0)) | r3_lattice3(sK0,X9,a_2_2_lattice3(X10,X11)) | sK6(sK0,X9,a_2_2_lattice3(X10,X11)) = sK7(sK6(sK0,X9,a_2_2_lattice3(X10,X11)),X10,X11) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10)) ) | ~spl9_14),
% 5.30/1.02    inference(resolution,[],[f190,f88])).
% 5.30/1.02  fof(f381,plain,(
% 5.30/1.02    spl9_37 | spl9_1 | ~spl9_4 | ~spl9_25),
% 5.30/1.02    inference(avatar_split_clause,[],[f309,f281,f122,f107,f379])).
% 5.30/1.02  fof(f281,plain,(
% 5.30/1.02    spl9_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 5.30/1.02  fof(f309,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_25)),
% 5.30/1.02    inference(subsumption_resolution,[],[f308,f109])).
% 5.30/1.02  fof(f308,plain,(
% 5.30/1.02    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | r3_lattice3(sK0,sK8(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_25)),
% 5.30/1.02    inference(resolution,[],[f282,f124])).
% 5.30/1.02  fof(f282,plain,(
% 5.30/1.02    ( ! [X2,X0,X1] : (~l3_lattices(X1) | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1)) ) | ~spl9_25),
% 5.30/1.02    inference(avatar_component_clause,[],[f281])).
% 5.30/1.02  fof(f348,plain,(
% 5.30/1.02    spl9_34 | ~spl9_14),
% 5.30/1.02    inference(avatar_split_clause,[],[f203,f189,f346])).
% 5.30/1.02  fof(f203,plain,(
% 5.30/1.02    ( ! [X6,X8,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | r3_lattice3(sK0,X6,a_2_2_lattice3(X7,X8)) | r4_lattice3(X7,sK7(sK6(sK0,X6,a_2_2_lattice3(X7,X8)),X7,X8),X8) | ~l3_lattices(X7) | ~v4_lattice3(X7) | ~v10_lattices(X7) | v2_struct_0(X7)) ) | ~spl9_14),
% 5.30/1.02    inference(resolution,[],[f190,f89])).
% 5.30/1.02  fof(f321,plain,(
% 5.30/1.02    spl9_29 | ~spl9_13),
% 5.30/1.02    inference(avatar_split_clause,[],[f198,f185,f319])).
% 5.30/1.02  fof(f198,plain,(
% 5.30/1.02    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5)) | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK8(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5) | ~l3_lattices(X4) | v2_struct_0(X4)) ) | ~spl9_13),
% 5.30/1.02    inference(resolution,[],[f186,f92])).
% 5.30/1.02  fof(f92,plain,(
% 5.30/1.02    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sK8(X0,X1,X2) = X0 | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.30/1.02    inference(cnf_transformation,[],[f58])).
% 5.30/1.02  fof(f307,plain,(
% 5.30/1.02    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | spl9_8 | spl9_27),
% 5.30/1.02    inference(avatar_contradiction_clause,[],[f306])).
% 5.30/1.02  fof(f306,plain,(
% 5.30/1.02    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f305,f109])).
% 5.30/1.02  fof(f305,plain,(
% 5.30/1.02    v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f304,f114])).
% 5.30/1.02  fof(f304,plain,(
% 5.30/1.02    ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_6 | ~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f303,f119])).
% 5.30/1.02  fof(f303,plain,(
% 5.30/1.02    ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_6 | ~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f302,f124])).
% 5.30/1.02  fof(f302,plain,(
% 5.30/1.02    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f301,f134])).
% 5.30/1.02  fof(f301,plain,(
% 5.30/1.02    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_7 | spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f300,f139])).
% 5.30/1.02  fof(f139,plain,(
% 5.30/1.02    r3_lattice3(sK0,sK1,sK2) | ~spl9_7),
% 5.30/1.02    inference(avatar_component_clause,[],[f137])).
% 5.30/1.02  fof(f137,plain,(
% 5.30/1.02    spl9_7 <=> r3_lattice3(sK0,sK1,sK2)),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 5.30/1.02  fof(f300,plain,(
% 5.30/1.02    ~r3_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl9_8 | spl9_27)),
% 5.30/1.02    inference(subsumption_resolution,[],[f298,f144])).
% 5.30/1.02  fof(f144,plain,(
% 5.30/1.02    sK1 != k16_lattice3(sK0,sK2) | spl9_8),
% 5.30/1.02    inference(avatar_component_clause,[],[f142])).
% 5.30/1.02  fof(f142,plain,(
% 5.30/1.02    spl9_8 <=> sK1 = k16_lattice3(sK0,sK2)),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 5.30/1.02  fof(f298,plain,(
% 5.30/1.02    sK1 = k16_lattice3(sK0,sK2) | ~r3_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | spl9_27),
% 5.30/1.02    inference(resolution,[],[f291,f71])).
% 5.30/1.02  fof(f71,plain,(
% 5.30/1.02    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k16_lattice3(X0,X2) = X1 | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.30/1.02    inference(cnf_transformation,[],[f37])).
% 5.30/1.02  fof(f37,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 5.30/1.02  fof(f36,plain,(
% 5.30/1.02    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 5.30/1.02    introduced(choice_axiom,[])).
% 5.30/1.02  fof(f35,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.02    inference(rectify,[],[f34])).
% 5.30/1.02  fof(f34,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.02    inference(flattening,[],[f33])).
% 5.30/1.02  fof(f33,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.02    inference(nnf_transformation,[],[f18])).
% 5.30/1.02  fof(f18,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.02    inference(flattening,[],[f17])).
% 5.30/1.02  fof(f17,plain,(
% 5.30/1.02    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.30/1.02    inference(ennf_transformation,[],[f6])).
% 5.30/1.02  fof(f6,axiom,(
% 5.30/1.02    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 5.30/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 5.30/1.02  fof(f291,plain,(
% 5.30/1.02    ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl9_27),
% 5.30/1.02    inference(avatar_component_clause,[],[f289])).
% 5.30/1.02  fof(f292,plain,(
% 5.30/1.02    spl9_26 | ~spl9_27 | ~spl9_10 | ~spl9_23),
% 5.30/1.02    inference(avatar_split_clause,[],[f274,f264,f159,f289,f285])).
% 5.30/1.02  fof(f159,plain,(
% 5.30/1.02    spl9_10 <=> ! [X1,X0] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_1_lattice3(sK0,X1)))),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 5.30/1.02  fof(f264,plain,(
% 5.30/1.02    spl9_23 <=> r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)),
% 5.30/1.02    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 5.30/1.03  fof(f274,plain,(
% 5.30/1.03    ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r2_hidden(sK3(sK0,sK1,sK2),a_2_1_lattice3(sK0,sK2)) | (~spl9_10 | ~spl9_23)),
% 5.30/1.03    inference(resolution,[],[f266,f160])).
% 5.30/1.03  fof(f160,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_1_lattice3(sK0,X1))) ) | ~spl9_10),
% 5.30/1.03    inference(avatar_component_clause,[],[f159])).
% 5.30/1.03  fof(f266,plain,(
% 5.30/1.03    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | ~spl9_23),
% 5.30/1.03    inference(avatar_component_clause,[],[f264])).
% 5.30/1.03  fof(f283,plain,(
% 5.30/1.03    spl9_25 | ~spl9_13),
% 5.30/1.03    inference(avatar_split_clause,[],[f197,f185,f281])).
% 5.30/1.03  fof(f197,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK8(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2) | ~l3_lattices(X1) | v2_struct_0(X1)) ) | ~spl9_13),
% 5.30/1.03    inference(resolution,[],[f186,f93])).
% 5.30/1.03  fof(f93,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK8(X0,X1,X2),X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f58])).
% 5.30/1.03  fof(f279,plain,(
% 5.30/1.03    ~spl9_24 | ~spl9_6 | ~spl9_7 | spl9_8 | ~spl9_22),
% 5.30/1.03    inference(avatar_split_clause,[],[f270,f257,f142,f137,f132,f276])).
% 5.30/1.03  fof(f257,plain,(
% 5.30/1.03    spl9_22 <=> ! [X1,X0] : (~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0)),
% 5.30/1.03    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 5.30/1.03  fof(f270,plain,(
% 5.30/1.03    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | (~spl9_6 | ~spl9_7 | spl9_8 | ~spl9_22)),
% 5.30/1.03    inference(subsumption_resolution,[],[f269,f144])).
% 5.30/1.03  fof(f269,plain,(
% 5.30/1.03    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | sK1 = k16_lattice3(sK0,sK2) | (~spl9_6 | ~spl9_7 | ~spl9_22)),
% 5.30/1.03    inference(subsumption_resolution,[],[f268,f134])).
% 5.30/1.03  fof(f268,plain,(
% 5.30/1.03    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k16_lattice3(sK0,sK2) | (~spl9_7 | ~spl9_22)),
% 5.30/1.03    inference(resolution,[],[f258,f139])).
% 5.30/1.03  fof(f258,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) ) | ~spl9_22),
% 5.30/1.03    inference(avatar_component_clause,[],[f257])).
% 5.30/1.03  fof(f267,plain,(
% 5.30/1.03    spl9_23 | ~spl9_6 | ~spl9_7 | spl9_8 | ~spl9_21),
% 5.30/1.03    inference(avatar_split_clause,[],[f262,f253,f142,f137,f132,f264])).
% 5.30/1.03  fof(f253,plain,(
% 5.30/1.03    spl9_21 <=> ! [X1,X0] : (r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0)),
% 5.30/1.03    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 5.30/1.03  fof(f262,plain,(
% 5.30/1.03    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | (~spl9_6 | ~spl9_7 | spl9_8 | ~spl9_21)),
% 5.30/1.03    inference(subsumption_resolution,[],[f261,f144])).
% 5.30/1.03  fof(f261,plain,(
% 5.30/1.03    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | sK1 = k16_lattice3(sK0,sK2) | (~spl9_6 | ~spl9_7 | ~spl9_21)),
% 5.30/1.03    inference(subsumption_resolution,[],[f260,f134])).
% 5.30/1.03  fof(f260,plain,(
% 5.30/1.03    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k16_lattice3(sK0,sK2) | (~spl9_7 | ~spl9_21)),
% 5.30/1.03    inference(resolution,[],[f254,f139])).
% 5.30/1.03  fof(f254,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) ) | ~spl9_21),
% 5.30/1.03    inference(avatar_component_clause,[],[f253])).
% 5.30/1.03  fof(f259,plain,(
% 5.30/1.03    spl9_22 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f231,f122,f117,f112,f107,f257])).
% 5.30/1.03  fof(f231,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f230,f109])).
% 5.30/1.03  fof(f230,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0 | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f229,f114])).
% 5.30/1.03  fof(f229,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f228,f124])).
% 5.30/1.03  fof(f228,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattices(sK0,sK3(sK0,X0,X1),X0) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k16_lattice3(sK0,X1) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_3),
% 5.30/1.03    inference(resolution,[],[f73,f119])).
% 5.30/1.03  fof(f73,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r3_lattices(X0,sK3(X0,X1,X2),X1) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k16_lattice3(X0,X2) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f37])).
% 5.30/1.03  fof(f255,plain,(
% 5.30/1.03    spl9_21 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f227,f122,f117,f112,f107,f253])).
% 5.30/1.03  fof(f227,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f226,f109])).
% 5.30/1.03  fof(f226,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0 | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f225,f114])).
% 5.30/1.03  fof(f225,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f224,f124])).
% 5.30/1.03  fof(f224,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattice3(sK0,sK3(sK0,X0,X1),X1) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k16_lattice3(sK0,X1) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_3),
% 5.30/1.03    inference(resolution,[],[f72,f119])).
% 5.30/1.03  fof(f72,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r3_lattice3(X0,sK3(X0,X1,X2),X2) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k16_lattice3(X0,X2) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f37])).
% 5.30/1.03  fof(f235,plain,(
% 5.30/1.03    spl9_18 | spl9_1 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f219,f122,f107,f233])).
% 5.30/1.03  fof(f219,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X0)) ) | (spl9_1 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f218,f109])).
% 5.30/1.03  fof(f218,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X0) | v2_struct_0(sK0)) ) | ~spl9_4),
% 5.30/1.03    inference(resolution,[],[f83,f124])).
% 5.30/1.03  fof(f83,plain,(
% 5.30/1.03    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X4) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f50])).
% 5.30/1.03  fof(f223,plain,(
% 5.30/1.03    spl9_17 | ~spl9_9 | ~spl9_16),
% 5.30/1.03    inference(avatar_split_clause,[],[f217,f214,f151,f221])).
% 5.30/1.03  fof(f151,plain,(
% 5.30/1.03    spl9_9 <=> ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))),
% 5.30/1.03    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 5.30/1.03  fof(f214,plain,(
% 5.30/1.03    spl9_16 <=> ! [X1,X0] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)))),
% 5.30/1.03    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 5.30/1.03  fof(f217,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattices(sK0,X1,k15_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0))) ) | (~spl9_9 | ~spl9_16)),
% 5.30/1.03    inference(superposition,[],[f215,f152])).
% 5.30/1.03  fof(f152,plain,(
% 5.30/1.03    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ) | ~spl9_9),
% 5.30/1.03    inference(avatar_component_clause,[],[f151])).
% 5.30/1.03  fof(f215,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1)) ) | ~spl9_16),
% 5.30/1.03    inference(avatar_component_clause,[],[f214])).
% 5.30/1.03  fof(f216,plain,(
% 5.30/1.03    spl9_16 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f212,f122,f117,f112,f107,f214])).
% 5.30/1.03  fof(f212,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f211,f109])).
% 5.30/1.03  fof(f211,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f210,f114])).
% 5.30/1.03  fof(f210,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f209,f124])).
% 5.30/1.03  fof(f209,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_3),
% 5.30/1.03    inference(resolution,[],[f68,f119])).
% 5.30/1.03  fof(f68,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f16])).
% 5.30/1.03  fof(f16,plain,(
% 5.30/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.03    inference(flattening,[],[f15])).
% 5.30/1.03  fof(f15,plain,(
% 5.30/1.03    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.30/1.03    inference(ennf_transformation,[],[f8])).
% 5.30/1.03  fof(f8,axiom,(
% 5.30/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 5.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).
% 5.30/1.03  fof(f191,plain,(
% 5.30/1.03    spl9_14 | spl9_1 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f163,f122,f107,f189])).
% 5.30/1.03  fof(f163,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1)) ) | (spl9_1 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f162,f109])).
% 5.30/1.03  fof(f162,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl9_4),
% 5.30/1.03    inference(resolution,[],[f85,f124])).
% 5.30/1.03  fof(f85,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK6(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f50])).
% 5.30/1.03  fof(f187,plain,(
% 5.30/1.03    spl9_13 | spl9_1 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f157,f122,f107,f185])).
% 5.30/1.03  fof(f157,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | (spl9_1 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f156,f109])).
% 5.30/1.03  fof(f156,plain,(
% 5.30/1.03    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl9_4),
% 5.30/1.03    inference(resolution,[],[f81,f124])).
% 5.30/1.03  fof(f81,plain,(
% 5.30/1.03    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK5(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f46])).
% 5.30/1.03  fof(f170,plain,(
% 5.30/1.03    spl9_11 | ~spl9_6 | ~spl9_7 | ~spl9_10),
% 5.30/1.03    inference(avatar_split_clause,[],[f165,f159,f137,f132,f167])).
% 5.30/1.03  fof(f165,plain,(
% 5.30/1.03    r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) | (~spl9_6 | ~spl9_7 | ~spl9_10)),
% 5.30/1.03    inference(subsumption_resolution,[],[f164,f134])).
% 5.30/1.03  fof(f164,plain,(
% 5.30/1.03    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) | (~spl9_7 | ~spl9_10)),
% 5.30/1.03    inference(resolution,[],[f160,f139])).
% 5.30/1.03  fof(f161,plain,(
% 5.30/1.03    spl9_10 | spl9_1 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f155,f122,f107,f159])).
% 5.30/1.03  fof(f155,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_1_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f154,f109])).
% 5.30/1.03  fof(f154,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) | v2_struct_0(sK0)) ) | ~spl9_4),
% 5.30/1.03    inference(resolution,[],[f100,f124])).
% 5.30/1.03  fof(f100,plain,(
% 5.30/1.03    ( ! [X2,X3,X1] : (~l3_lattices(X1) | ~r3_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(X3,a_2_1_lattice3(X1,X2)) | v2_struct_0(X1)) )),
% 5.30/1.03    inference(equality_resolution,[],[f94])).
% 5.30/1.03  fof(f94,plain,(
% 5.30/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f58])).
% 5.30/1.03  fof(f153,plain,(
% 5.30/1.03    spl9_9 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f149,f122,f117,f112,f107,f151])).
% 5.30/1.03  fof(f149,plain,(
% 5.30/1.03    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f148,f109])).
% 5.30/1.03  fof(f148,plain,(
% 5.30/1.03    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f147,f114])).
% 5.30/1.03  fof(f147,plain,(
% 5.30/1.03    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl9_3 | ~spl9_4)),
% 5.30/1.03    inference(subsumption_resolution,[],[f146,f124])).
% 5.30/1.03  fof(f146,plain,(
% 5.30/1.03    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_3),
% 5.30/1.03    inference(resolution,[],[f67,f119])).
% 5.30/1.03  fof(f67,plain,(
% 5.30/1.03    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.30/1.03    inference(cnf_transformation,[],[f14])).
% 5.30/1.03  fof(f14,plain,(
% 5.30/1.03    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.30/1.03    inference(flattening,[],[f13])).
% 5.30/1.03  fof(f13,plain,(
% 5.30/1.03    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.30/1.03    inference(ennf_transformation,[],[f7])).
% 5.30/1.03  fof(f7,axiom,(
% 5.30/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 5.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 5.30/1.03  fof(f145,plain,(
% 5.30/1.03    ~spl9_8),
% 5.30/1.03    inference(avatar_split_clause,[],[f66,f142])).
% 5.30/1.03  fof(f66,plain,(
% 5.30/1.03    sK1 != k16_lattice3(sK0,sK2)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f32,plain,(
% 5.30/1.03    ((sK1 != k16_lattice3(sK0,sK2) & r3_lattice3(sK0,sK1,sK2) & r2_hidden(sK1,sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 5.30/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).
% 5.30/1.03  fof(f29,plain,(
% 5.30/1.03    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK0,X2) != X1 & r3_lattice3(sK0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 5.30/1.03    introduced(choice_axiom,[])).
% 5.30/1.03  fof(f30,plain,(
% 5.30/1.03    ? [X1] : (? [X2] : (k16_lattice3(sK0,X2) != X1 & r3_lattice3(sK0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k16_lattice3(sK0,X2) != sK1 & r3_lattice3(sK0,sK1,X2) & r2_hidden(sK1,X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 5.30/1.03    introduced(choice_axiom,[])).
% 5.30/1.03  fof(f31,plain,(
% 5.30/1.03    ? [X2] : (k16_lattice3(sK0,X2) != sK1 & r3_lattice3(sK0,sK1,X2) & r2_hidden(sK1,X2)) => (sK1 != k16_lattice3(sK0,sK2) & r3_lattice3(sK0,sK1,sK2) & r2_hidden(sK1,sK2))),
% 5.30/1.03    introduced(choice_axiom,[])).
% 5.30/1.03  fof(f12,plain,(
% 5.30/1.03    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 5.30/1.03    inference(flattening,[],[f11])).
% 5.30/1.03  fof(f11,plain,(
% 5.30/1.03    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.30/1.03    inference(ennf_transformation,[],[f10])).
% 5.30/1.03  fof(f10,negated_conjecture,(
% 5.30/1.03    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 5.30/1.03    inference(negated_conjecture,[],[f9])).
% 5.30/1.03  fof(f9,conjecture,(
% 5.30/1.03    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 5.30/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 5.30/1.03  fof(f140,plain,(
% 5.30/1.03    spl9_7),
% 5.30/1.03    inference(avatar_split_clause,[],[f65,f137])).
% 5.30/1.03  fof(f65,plain,(
% 5.30/1.03    r3_lattice3(sK0,sK1,sK2)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f135,plain,(
% 5.30/1.03    spl9_6),
% 5.30/1.03    inference(avatar_split_clause,[],[f63,f132])).
% 5.30/1.03  fof(f63,plain,(
% 5.30/1.03    m1_subset_1(sK1,u1_struct_0(sK0))),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f130,plain,(
% 5.30/1.03    spl9_5),
% 5.30/1.03    inference(avatar_split_clause,[],[f64,f127])).
% 5.30/1.03  fof(f64,plain,(
% 5.30/1.03    r2_hidden(sK1,sK2)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f125,plain,(
% 5.30/1.03    spl9_4),
% 5.30/1.03    inference(avatar_split_clause,[],[f62,f122])).
% 5.30/1.03  fof(f62,plain,(
% 5.30/1.03    l3_lattices(sK0)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f120,plain,(
% 5.30/1.03    spl9_3),
% 5.30/1.03    inference(avatar_split_clause,[],[f61,f117])).
% 5.30/1.03  fof(f61,plain,(
% 5.30/1.03    v4_lattice3(sK0)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f115,plain,(
% 5.30/1.03    spl9_2),
% 5.30/1.03    inference(avatar_split_clause,[],[f60,f112])).
% 5.30/1.03  fof(f60,plain,(
% 5.30/1.03    v10_lattices(sK0)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  fof(f110,plain,(
% 5.30/1.03    ~spl9_1),
% 5.30/1.03    inference(avatar_split_clause,[],[f59,f107])).
% 5.30/1.03  fof(f59,plain,(
% 5.30/1.03    ~v2_struct_0(sK0)),
% 5.30/1.03    inference(cnf_transformation,[],[f32])).
% 5.30/1.03  % SZS output end Proof for theBenchmark
% 5.30/1.03  % (28102)------------------------------
% 5.30/1.03  % (28102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.30/1.03  % (28102)Termination reason: Refutation
% 5.30/1.03  
% 5.30/1.03  % (28102)Memory used [KB]: 14200
% 5.30/1.03  % (28102)Time elapsed: 0.585 s
% 5.30/1.03  % (28102)------------------------------
% 5.30/1.03  % (28102)------------------------------
% 5.30/1.03  % (28099)Success in time 0.672 s
%------------------------------------------------------------------------------
