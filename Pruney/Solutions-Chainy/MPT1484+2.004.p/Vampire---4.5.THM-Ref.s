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
% DateTime   : Thu Dec  3 13:15:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 317 expanded)
%              Number of leaves         :   38 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  874 (1742 expanded)
%              Number of equality atoms :   90 ( 204 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1858,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f96,f100,f104,f108,f118,f124,f133,f139,f142,f147,f163,f184,f209,f688,f1187,f1395,f1425,f1485,f1829,f1839,f1853])).

fof(f1853,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_12
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_237 ),
    inference(avatar_split_clause,[],[f1851,f1837,f161,f122,f131,f86,f82])).

fof(f82,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f131,plain,
    ( spl5_12
  <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f122,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f161,plain,
    ( spl5_16
  <=> k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1837,plain,
    ( spl5_237
  <=> sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f1851,plain,
    ( sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f1844,f162])).

fof(f162,plain,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1844,plain,
    ( sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_237 ),
    inference(superposition,[],[f1838,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1838,plain,
    ( sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2)
    | ~ spl5_237 ),
    inference(avatar_component_clause,[],[f1837])).

fof(f1839,plain,
    ( spl5_237
    | ~ spl5_3
    | ~ spl5_236 ),
    inference(avatar_split_clause,[],[f1832,f1827,f86,f1837])).

fof(f1827,plain,
    ( spl5_236
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).

fof(f1832,plain,
    ( sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2)
    | ~ spl5_3
    | ~ spl5_236 ),
    inference(resolution,[],[f1828,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1828,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2) )
    | ~ spl5_236 ),
    inference(avatar_component_clause,[],[f1827])).

fof(f1829,plain,
    ( ~ spl5_2
    | spl5_236
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_214 ),
    inference(avatar_split_clause,[],[f1825,f1423,f182,f82,f1827,f82])).

fof(f182,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1423,plain,
    ( spl5_214
  <=> ! [X3,X2] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).

fof(f1825,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_214 ),
    inference(duplicate_literal_removal,[],[f1819])).

fof(f1819,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_20
    | ~ spl5_214 ),
    inference(resolution,[],[f1811,f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1811,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK2,X0),sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2) )
    | ~ spl5_2
    | ~ spl5_214 ),
    inference(resolution,[],[f1424,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f1424,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2) )
    | ~ spl5_214 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f1485,plain,
    ( spl5_19
    | ~ spl5_8
    | ~ spl5_4
    | ~ spl5_2
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1484,f1339,f82,f90,f106,f179])).

fof(f179,plain,
    ( spl5_19
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f106,plain,
    ( spl5_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f90,plain,
    ( spl5_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1339,plain,
    ( spl5_201
  <=> r1_orders_2(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f1484,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_201 ),
    inference(resolution,[],[f1394,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f1394,plain,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | spl5_201 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1425,plain,
    ( ~ spl5_4
    | spl5_214
    | ~ spl5_208 ),
    inference(avatar_split_clause,[],[f1410,f1392,f1423,f90])).

fof(f1392,plain,
    ( spl5_208
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f1410,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2)
        | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_208 ),
    inference(resolution,[],[f1393,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f1393,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2)
        | sK2 = k10_lattice3(sK0,X0,sK2) )
    | ~ spl5_208 ),
    inference(avatar_component_clause,[],[f1392])).

fof(f1395,plain,
    ( spl5_208
    | ~ spl5_201
    | ~ spl5_2
    | ~ spl5_177 ),
    inference(avatar_split_clause,[],[f1387,f1185,f82,f1339,f1392])).

fof(f1185,plain,
    ( spl5_177
  <=> ! [X3,X2] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1387,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,sK2)
        | ~ r1_orders_2(sK0,X0,sK2)
        | sK2 = k10_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_177 ),
    inference(resolution,[],[f1186,f83])).

fof(f1186,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | k10_lattice3(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_177 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1187,plain,
    ( spl5_19
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_4
    | spl5_177
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f1178,f686,f1185,f90,f98,f102,f179])).

fof(f102,plain,
    ( spl5_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f98,plain,
    ( spl5_6
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f686,plain,
    ( spl5_92
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1178,plain,
    ( ! [X2,X3] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_92 ),
    inference(duplicate_literal_removal,[],[f1177])).

fof(f1177,plain,
    ( ! [X2,X3] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X3,X3)
        | k10_lattice3(sK0,X2,X3) = X3
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_92 ),
    inference(resolution,[],[f687,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(f687,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f686])).

fof(f688,plain,
    ( spl5_19
    | ~ spl5_6
    | ~ spl5_4
    | spl5_92
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f684,f102,f686,f90,f98,f179])).

fof(f684,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | k10_lattice3(sK0,X1,X2) = X0
        | v2_struct_0(sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f59,f103])).

fof(f103,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | k10_lattice3(X0,X1,X2) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f209,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f208,f179,f98,f90])).

fof(f208,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f180,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (1250)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f184,plain,
    ( spl5_19
    | ~ spl5_7
    | ~ spl5_4
    | spl5_20
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f177,f94,f182,f90,f102,f179])).

fof(f94,plain,
    ( spl5_5
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f109,f95])).

fof(f95,plain,
    ( v2_lattice3(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f76,f70])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f163,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f157,f145,f86,f82,f161])).

fof(f145,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f157,plain,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(resolution,[],[f148,f87])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X0,sK2) = k12_lattice3(sK0,sK2,X0) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(resolution,[],[f146,f83])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f147,plain,
    ( ~ spl5_7
    | ~ spl5_4
    | spl5_14
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f143,f94,f145,f90,f102])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1)
        | ~ v5_orders_2(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f69,f95])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(f142,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f140,f137,f127,f86,f82])).

fof(f127,plain,
    ( spl5_11
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

% (1243)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f137,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl5_11
    | ~ spl5_13 ),
    inference(resolution,[],[f138,f128])).

fof(f128,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( ~ spl5_4
    | spl5_13
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f135,f122,f137,f90])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_10 ),
    inference(superposition,[],[f70,f123])).

fof(f133,plain,
    ( ~ spl5_11
    | ~ spl5_2
    | ~ spl5_12
    | spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f125,f116,f78,f131,f82,f127])).

fof(f78,plain,
    ( spl5_1
  <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f116,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f125,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_9 ),
    inference(superposition,[],[f79,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f79,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f124,plain,
    ( ~ spl5_7
    | ~ spl5_4
    | spl5_10
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f119,f94,f122,f90,f102])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ v5_orders_2(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f68,f95])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f118,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f112,f102,f116,f90,f98])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f67,f103])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f108,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f43,f106])).

fof(f43,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

fof(f104,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

% (1239)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f88,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f49,f82])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f78])).

fof(f50,plain,(
    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (1242)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (1241)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1249)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (1240)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (1247)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (1237)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (1251)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (1237)Refutation not found, incomplete strategy% (1237)------------------------------
% 0.21/0.49  % (1237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1237)Memory used [KB]: 10618
% 0.21/0.49  % (1237)Time elapsed: 0.080 s
% 0.21/0.49  % (1237)------------------------------
% 0.21/0.49  % (1237)------------------------------
% 0.21/0.50  % (1246)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (1254)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (1252)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (1236)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (1242)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1858,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f96,f100,f104,f108,f118,f124,f133,f139,f142,f147,f163,f184,f209,f688,f1187,f1395,f1425,f1485,f1829,f1839,f1853])).
% 0.21/0.50  fof(f1853,plain,(
% 0.21/0.50    ~spl5_2 | ~spl5_3 | spl5_12 | ~spl5_10 | ~spl5_16 | ~spl5_237),
% 0.21/0.50    inference(avatar_split_clause,[],[f1851,f1837,f161,f122,f131,f86,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl5_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl5_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl5_12 <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl5_10 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl5_16 <=> k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f1837,plain,(
% 0.21/0.50    spl5_237 <=> sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).
% 0.21/0.50  fof(f1851,plain,(
% 0.21/0.50    sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl5_10 | ~spl5_16 | ~spl5_237)),
% 0.21/0.50    inference(forward_demodulation,[],[f1844,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) | ~spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f161])).
% 0.21/0.50  fof(f1844,plain,(
% 0.21/0.50    sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl5_10 | ~spl5_237)),
% 0.21/0.50    inference(superposition,[],[f1838,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f1838,plain,(
% 0.21/0.50    sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2) | ~spl5_237),
% 0.21/0.50    inference(avatar_component_clause,[],[f1837])).
% 0.21/0.50  fof(f1839,plain,(
% 0.21/0.50    spl5_237 | ~spl5_3 | ~spl5_236),
% 0.21/0.50    inference(avatar_split_clause,[],[f1832,f1827,f86,f1837])).
% 0.21/0.50  fof(f1827,plain,(
% 0.21/0.50    spl5_236 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).
% 0.21/0.50  fof(f1832,plain,(
% 0.21/0.50    sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,sK1),sK2) | (~spl5_3 | ~spl5_236)),
% 0.21/0.50    inference(resolution,[],[f1828,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f1828,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2)) ) | ~spl5_236),
% 0.21/0.50    inference(avatar_component_clause,[],[f1827])).
% 0.21/0.50  fof(f1829,plain,(
% 0.21/0.50    ~spl5_2 | spl5_236 | ~spl5_2 | ~spl5_20 | ~spl5_214),
% 0.21/0.50    inference(avatar_split_clause,[],[f1825,f1423,f182,f82,f1827,f82])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl5_20 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f1423,plain,(
% 0.21/0.50    spl5_214 <=> ! [X3,X2] : (~r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_214])])).
% 0.21/0.50  fof(f1825,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_20 | ~spl5_214)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1819])).
% 0.21/0.50  fof(f1819,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_20 | ~spl5_214)),
% 0.21/0.50    inference(resolution,[],[f1811,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f1811,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_orders_2(sK0,k11_lattice3(sK0,sK2,X0),sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,sK2,X0),sK2)) ) | (~spl5_2 | ~spl5_214)),
% 0.21/0.50    inference(resolution,[],[f1424,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f1424,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2)) ) | ~spl5_214),
% 0.21/0.50    inference(avatar_component_clause,[],[f1423])).
% 0.21/0.50  fof(f1485,plain,(
% 0.21/0.50    spl5_19 | ~spl5_8 | ~spl5_4 | ~spl5_2 | spl5_201),
% 0.21/0.50    inference(avatar_split_clause,[],[f1484,f1339,f82,f90,f106,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl5_19 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl5_8 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl5_4 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f1339,plain,(
% 0.21/0.50    spl5_201 <=> r1_orders_2(sK0,sK2,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).
% 0.21/0.50  fof(f1484,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_201),
% 0.21/0.50    inference(resolution,[],[f1394,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.21/0.50  fof(f1394,plain,(
% 0.21/0.50    ~r1_orders_2(sK0,sK2,sK2) | spl5_201),
% 0.21/0.50    inference(avatar_component_clause,[],[f1339])).
% 0.21/0.50  fof(f1425,plain,(
% 0.21/0.50    ~spl5_4 | spl5_214 | ~spl5_208),
% 0.21/0.50    inference(avatar_split_clause,[],[f1410,f1392,f1423,f90])).
% 0.21/0.50  fof(f1392,plain,(
% 0.21/0.50    spl5_208 <=> ! [X0] : (~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,X0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).
% 0.21/0.50  fof(f1410,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_orders_2(sK0,k11_lattice3(sK0,X2,X3),sK2) | sK2 = k10_lattice3(sK0,k11_lattice3(sK0,X2,X3),sK2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl5_208),
% 0.21/0.50    inference(resolution,[],[f1393,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.21/0.50  fof(f1393,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2) | sK2 = k10_lattice3(sK0,X0,sK2)) ) | ~spl5_208),
% 0.21/0.50    inference(avatar_component_clause,[],[f1392])).
% 0.21/0.50  fof(f1395,plain,(
% 0.21/0.50    spl5_208 | ~spl5_201 | ~spl5_2 | ~spl5_177),
% 0.21/0.50    inference(avatar_split_clause,[],[f1387,f1185,f82,f1339,f1392])).
% 0.21/0.50  fof(f1185,plain,(
% 0.21/0.50    spl5_177 <=> ! [X3,X2] : (k10_lattice3(sK0,X2,X3) = X3 | ~r1_orders_2(sK0,X3,X3) | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).
% 0.21/0.50  fof(f1387,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_orders_2(sK0,sK2,sK2) | ~r1_orders_2(sK0,X0,sK2) | sK2 = k10_lattice3(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl5_2 | ~spl5_177)),
% 0.21/0.50    inference(resolution,[],[f1186,f83])).
% 0.21/0.50  fof(f1186,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X3) | ~r1_orders_2(sK0,X2,X3) | k10_lattice3(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl5_177),
% 0.21/0.50    inference(avatar_component_clause,[],[f1185])).
% 0.21/0.50  fof(f1187,plain,(
% 0.21/0.50    spl5_19 | ~spl5_7 | ~spl5_6 | ~spl5_4 | spl5_177 | ~spl5_92),
% 0.21/0.50    inference(avatar_split_clause,[],[f1178,f686,f1185,f90,f98,f102,f179])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_7 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl5_6 <=> v1_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f686,plain,(
% 0.21/0.50    spl5_92 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | k10_lattice3(sK0,X1,X2) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 0.21/0.50  fof(f1178,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k10_lattice3(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X3,X3) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_92),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1177])).
% 0.21/0.50  fof(f1177,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k10_lattice3(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X3,X3) | k10_lattice3(sK0,X2,X3) = X3 | ~r1_orders_2(sK0,X3,X3) | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_92),
% 0.21/0.50    inference(resolution,[],[f687,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.21/0.50  fof(f687,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | k10_lattice3(sK0,X1,X2) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X2,X0)) ) | ~spl5_92),
% 0.21/0.50    inference(avatar_component_clause,[],[f686])).
% 0.21/0.50  fof(f688,plain,(
% 0.21/0.50    spl5_19 | ~spl5_6 | ~spl5_4 | spl5_92 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f684,f102,f686,f90,f98,f179])).
% 0.21/0.50  fof(f684,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | k10_lattice3(sK0,X1,X2) = X0 | v2_struct_0(sK0)) ) | ~spl5_7),
% 0.21/0.50    inference(resolution,[],[f59,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | k10_lattice3(X0,X1,X2) = X3 | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~spl5_4 | ~spl5_6 | ~spl5_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f208,f179,f98,f90])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl5_19),
% 0.21/0.50    inference(resolution,[],[f180,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  % (1250)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f179])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl5_19 | ~spl5_7 | ~spl5_4 | spl5_20 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f177,f94,f182,f90,f102,f179])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_5 <=> v2_lattice3(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),X1) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f109,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    v2_lattice3(sK0) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f70])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl5_16 | ~spl5_2 | ~spl5_3 | ~spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f157,f145,f86,f82,f161])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl5_14 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_14)),
% 0.21/0.50    inference(resolution,[],[f148,f87])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X0,sK2) = k12_lattice3(sK0,sK2,X0)) ) | (~spl5_2 | ~spl5_14)),
% 0.21/0.50    inference(resolution,[],[f146,f83])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ~spl5_7 | ~spl5_4 | spl5_14 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f143,f94,f145,f90,f102])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k12_lattice3(sK0,X1,X0) = k12_lattice3(sK0,X0,X1) | ~v5_orders_2(sK0)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f69,f95])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~spl5_2 | ~spl5_3 | spl5_11 | ~spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f137,f127,f86,f82])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl5_11 <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  % (1243)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl5_13 <=> ! [X1,X0] : (m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (spl5_11 | ~spl5_13)),
% 0.21/0.50    inference(resolution,[],[f138,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f127])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~spl5_4 | spl5_13 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f135,f122,f137,f90])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl5_10),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_10),
% 0.21/0.50    inference(superposition,[],[f70,f123])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ~spl5_11 | ~spl5_2 | ~spl5_12 | spl5_1 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f125,f116,f78,f131,f82,f127])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl5_1 <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl5_9 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl5_1 | ~spl5_9)),
% 0.21/0.50    inference(superposition,[],[f79,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~spl5_7 | ~spl5_4 | spl5_10 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f94,f122,f90,f102])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) | ~v5_orders_2(sK0)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f68,f95])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_4 | spl5_9 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f112,f102,f116,f90,f98])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)) ) | ~spl5_7),
% 0.21/0.50    inference(resolution,[],[f67,f103])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f106])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ((sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) => (sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f102])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f98])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v1_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f94])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v2_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f90])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  % (1239)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f86])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f82])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f78])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1242)------------------------------
% 0.21/0.50  % (1242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1242)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1242)Memory used [KB]: 12153
% 0.21/0.50  % (1242)Time elapsed: 0.093 s
% 0.21/0.50  % (1242)------------------------------
% 0.21/0.50  % (1242)------------------------------
% 0.21/0.50  % (1257)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (1233)Success in time 0.148 s
%------------------------------------------------------------------------------
