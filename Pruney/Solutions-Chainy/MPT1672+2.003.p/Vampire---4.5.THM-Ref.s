%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:16 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 480 expanded)
%              Number of leaves         :   32 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  844 (2882 expanded)
%              Number of equality atoms :   43 ( 242 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f81,f108,f189,f194,f204,f228,f299,f338,f376,f418,f476,f550,f723,f827,f954,f963,f976,f1359,f1390,f1411])).

fof(f1411,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_74 ),
    inference(avatar_contradiction_clause,[],[f1410])).

fof(f1410,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f1409,f240])).

fof(f240,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_8
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1409,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f1408,f75])).

fof(f75,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1408,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f1403,f80])).

fof(f80,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1403,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_74 ),
    inference(resolution,[],[f1389,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1389,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1388,plain,
    ( spl7_74
  <=> r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f1390,plain,
    ( spl7_74
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f1369,f1357,f474,f416,f297,f79,f74,f1388])).

fof(f297,plain,
    ( spl7_26
  <=> r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f416,plain,
    ( spl7_32
  <=> sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f474,plain,
    ( spl7_34
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1357,plain,
    ( spl7_72
  <=> r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f1369,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f1360,f80])).

fof(f1360,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | ~ spl7_2
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_72 ),
    inference(resolution,[],[f1358,f997])).

fof(f997,plain,
    ( ! [X10] :
        ( ~ r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10) )
    | ~ spl7_2
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f518,f298])).

fof(f298,plain,
    ( r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f297])).

fof(f518,plain,
    ( ! [X10] :
        ( ~ r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10)
        | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10) )
    | ~ spl7_2
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f517,f75])).

fof(f517,plain,
    ( ! [X10] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10)
        | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10) )
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f515,f475])).

fof(f475,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f474])).

fof(f515,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10)
        | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10) )
    | ~ spl7_32 ),
    inference(superposition,[],[f68,f417])).

fof(f417,plain,
    ( sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f416])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f1358,plain,
    ( r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1359,plain,
    ( spl7_72
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f1355,f374,f103,f79,f74,f1357])).

fof(f103,plain,
    ( spl7_7
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f374,plain,
    ( spl7_30
  <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1355,plain,
    ( r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1354,f75])).

fof(f1354,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1353,f80])).

fof(f1353,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(resolution,[],[f413,f104])).

fof(f104,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(X0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | r2_lattice3(X0,sK4(sK5(sK0,sK2,sK3)),X1) )
    | ~ spl7_30 ),
    inference(resolution,[],[f375,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f375,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f374])).

fof(f976,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_57 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f974,f116])).

fof(f116,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f974,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f973,f75])).

fof(f973,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f968,f80])).

fof(f968,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_57 ),
    inference(resolution,[],[f950,f47])).

fof(f950,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f949])).

fof(f949,plain,
    ( spl7_57
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f963,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_58 ),
    inference(avatar_contradiction_clause,[],[f962])).

fof(f962,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_58 ),
    inference(subsumption_resolution,[],[f961,f116])).

fof(f961,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_58 ),
    inference(resolution,[],[f953,f86])).

fof(f86,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f83,f75])).

fof(f83,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f953,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_58 ),
    inference(avatar_component_clause,[],[f952])).

fof(f952,plain,
    ( spl7_58
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f954,plain,
    ( spl7_57
    | ~ spl7_58
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f842,f825,f79,f74,f952,f949])).

fof(f825,plain,
    ( spl7_52
  <=> r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f842,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f841,f75])).

fof(f841,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ spl7_3
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f835,f80])).

fof(f835,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)
    | ~ spl7_52 ),
    inference(resolution,[],[f826,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f826,plain,
    ( r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f825])).

fof(f827,plain,
    ( spl7_52
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f812,f721,f192,f79,f74,f70,f825])).

fof(f70,plain,
    ( spl7_1
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f192,plain,
    ( spl7_17
  <=> r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f721,plain,
    ( spl7_48
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f812,plain,
    ( r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(resolution,[],[f731,f193])).

fof(f193,plain,
    ( r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f731,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f730,f71])).

fof(f71,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f730,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f729,f80])).

fof(f729,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f728,f77])).

fof(f77,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f728,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f724,f75])).

fof(f724,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_48 ),
    inference(resolution,[],[f722,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f722,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f721])).

fof(f723,plain,
    ( spl7_48
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f683,f226,f106,f79,f74,f721])).

fof(f226,plain,
    ( spl7_18
  <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f683,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f682,f80])).

fof(f682,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(resolution,[],[f555,f107])).

fof(f107,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f227,f139])).

fof(f139,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(k1_yellow_0(sK0,X7),X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK0,X7),X6)
        | ~ r2_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f134,f75])).

fof(f134,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(k1_yellow_0(sK0,X7),X8)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X7),X6)
        | ~ r2_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f227,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f550,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f109,f106,f103])).

fof(f109,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f36,f107])).

fof(f36,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f476,plain,
    ( spl7_34
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f454,f416,f74,f474])).

fof(f454,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(superposition,[],[f77,f417])).

fof(f418,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f402,f106,f79,f74,f416])).

fof(f402,plain,
    ( sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f333,f240])).

fof(f333,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f152,f87])).

fof(f87,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK0,X3,sK3),X3)
        | r2_lattice3(sK0,X3,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f84,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,X3,sK3),X3)
        | r2_lattice3(sK0,X3,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | sK5(sK0,X0,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,X0,sK3))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k1_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f376,plain,
    ( spl7_30
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f370,f336,f374])).

fof(f336,plain,
    ( spl7_28
  <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f370,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f337,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f337,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f336])).

fof(f338,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f316,f106,f79,f74,f336])).

fof(f316,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f294,f240])).

fof(f294,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f153,f87])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK0,X1,sK3),sK2)
        | r2_lattice3(sK0,X1,sK3)
        | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f86,f32])).

fof(f32,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f299,plain,
    ( spl7_26
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f292,f106,f79,f74,f297])).

fof(f292,plain,
    ( r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f291,f240])).

fof(f291,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f154,f87])).

fof(f154,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK0,X2,sK3),sK2)
        | r2_lattice3(sK0,X2,sK3)
        | r1_yellow_0(sK0,sK4(sK5(sK0,X2,sK3))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f86,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | r1_yellow_0(sK0,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f228,plain,
    ( spl7_18
    | spl7_16
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f177,f103,f79,f74,f187,f226])).

fof(f187,plain,
    ( spl7_16
  <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f177,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f176,f60])).

fof(f60,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f176,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f174,f116])).

fof(f174,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f151,f38])).

fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0))
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f204,plain,(
    ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f197,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f197,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_16 ),
    inference(superposition,[],[f66,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f194,plain,
    ( spl7_17
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f190,f184,f74,f192])).

fof(f184,plain,
    ( spl7_15
  <=> r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f190,plain,
    ( r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(resolution,[],[f185,f138])).

fof(f138,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f130,f75])).

fof(f130,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f185,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f189,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f179,f103,f79,f74,f187,f184])).

fof(f179,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f178,f60])).

fof(f178,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f175,f116])).

fof(f175,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f151,f39])).

fof(f39,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | r1_yellow_0(sK0,X6) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f108,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f35,f106,f103])).

fof(f35,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f43,f74])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f42,f70])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:24:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (26605)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.42  % (26603)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.44  % (26596)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (26597)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (26604)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26593)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (26594)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (26595)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (26590)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (26599)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (26601)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (26591)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (26610)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (26608)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (26609)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (26602)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26600)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (26606)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.53  % (26598)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (26592)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (26607)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 2.10/0.63  % (26590)Refutation found. Thanks to Tanya!
% 2.10/0.63  % SZS status Theorem for theBenchmark
% 2.10/0.63  % SZS output start Proof for theBenchmark
% 2.10/0.63  fof(f1426,plain,(
% 2.10/0.63    $false),
% 2.10/0.63    inference(avatar_sat_refutation,[],[f72,f76,f81,f108,f189,f194,f204,f228,f299,f338,f376,f418,f476,f550,f723,f827,f954,f963,f976,f1359,f1390,f1411])).
% 2.10/0.63  fof(f1411,plain,(
% 2.10/0.63    ~spl7_2 | ~spl7_3 | spl7_8 | ~spl7_74),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f1410])).
% 2.10/0.63  fof(f1410,plain,(
% 2.10/0.63    $false | (~spl7_2 | ~spl7_3 | spl7_8 | ~spl7_74)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1409,f240])).
% 2.10/0.63  fof(f240,plain,(
% 2.10/0.63    ~r2_lattice3(sK0,sK2,sK3) | spl7_8),
% 2.10/0.63    inference(avatar_component_clause,[],[f106])).
% 2.10/0.63  fof(f106,plain,(
% 2.10/0.63    spl7_8 <=> r2_lattice3(sK0,sK2,sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.10/0.63  fof(f1409,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_74)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1408,f75])).
% 2.10/0.63  fof(f75,plain,(
% 2.10/0.63    l1_orders_2(sK0) | ~spl7_2),
% 2.10/0.63    inference(avatar_component_clause,[],[f74])).
% 2.10/0.63  fof(f74,plain,(
% 2.10/0.63    spl7_2 <=> l1_orders_2(sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.10/0.63  fof(f1408,plain,(
% 2.10/0.63    ~l1_orders_2(sK0) | r2_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_74)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1403,f80])).
% 2.10/0.63  fof(f80,plain,(
% 2.10/0.63    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_3),
% 2.10/0.63    inference(avatar_component_clause,[],[f79])).
% 2.10/0.63  fof(f79,plain,(
% 2.10/0.63    spl7_3 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.10/0.63  fof(f1403,plain,(
% 2.10/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK2,sK3) | ~spl7_74),
% 2.10/0.63    inference(resolution,[],[f1389,f47])).
% 2.10/0.63  fof(f47,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f21])).
% 2.10/0.63  fof(f21,plain,(
% 2.10/0.63    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(flattening,[],[f20])).
% 2.10/0.63  fof(f20,plain,(
% 2.10/0.63    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f6])).
% 2.10/0.63  fof(f6,axiom,(
% 2.10/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 2.10/0.63  fof(f1389,plain,(
% 2.10/0.63    r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3) | ~spl7_74),
% 2.10/0.63    inference(avatar_component_clause,[],[f1388])).
% 2.10/0.63  fof(f1388,plain,(
% 2.10/0.63    spl7_74 <=> r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 2.10/0.63  fof(f1390,plain,(
% 2.10/0.63    spl7_74 | ~spl7_2 | ~spl7_3 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_72),
% 2.10/0.63    inference(avatar_split_clause,[],[f1369,f1357,f474,f416,f297,f79,f74,f1388])).
% 2.10/0.63  fof(f297,plain,(
% 2.10/0.63    spl7_26 <=> r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.10/0.63  fof(f416,plain,(
% 2.10/0.63    spl7_32 <=> sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.10/0.63  fof(f474,plain,(
% 2.10/0.63    spl7_34 <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.10/0.63  fof(f1357,plain,(
% 2.10/0.63    spl7_72 <=> r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 2.10/0.63  fof(f1369,plain,(
% 2.10/0.63    r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3) | (~spl7_2 | ~spl7_3 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_72)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1360,f80])).
% 2.10/0.63  fof(f1360,plain,(
% 2.10/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3) | (~spl7_2 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_72)),
% 2.10/0.63    inference(resolution,[],[f1358,f997])).
% 2.10/0.63  fof(f997,plain,(
% 2.10/0.63    ( ! [X10] : (~r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10)) ) | (~spl7_2 | ~spl7_26 | ~spl7_32 | ~spl7_34)),
% 2.10/0.63    inference(subsumption_resolution,[],[f518,f298])).
% 2.10/0.63  fof(f298,plain,(
% 2.10/0.63    r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_26),
% 2.10/0.63    inference(avatar_component_clause,[],[f297])).
% 2.10/0.63  fof(f518,plain,(
% 2.10/0.63    ( ! [X10] : (~r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10) | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10)) ) | (~spl7_2 | ~spl7_32 | ~spl7_34)),
% 2.10/0.63    inference(subsumption_resolution,[],[f517,f75])).
% 2.10/0.63  fof(f517,plain,(
% 2.10/0.63    ( ! [X10] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10) | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10)) ) | (~spl7_32 | ~spl7_34)),
% 2.10/0.63    inference(subsumption_resolution,[],[f515,f475])).
% 2.10/0.63  fof(f475,plain,(
% 2.10/0.63    m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_34),
% 2.10/0.63    inference(avatar_component_clause,[],[f474])).
% 2.10/0.63  fof(f515,plain,(
% 2.10/0.63    ( ! [X10] : (~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X10) | r1_orders_2(sK0,sK5(sK0,sK2,sK3),X10)) ) | ~spl7_32),
% 2.10/0.63    inference(superposition,[],[f68,f417])).
% 2.10/0.63  fof(f417,plain,(
% 2.10/0.63    sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_32),
% 2.10/0.63    inference(avatar_component_clause,[],[f416])).
% 2.10/0.63  fof(f68,plain,(
% 2.10/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 2.10/0.63    inference(equality_resolution,[],[f56])).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 2.10/0.63    inference(cnf_transformation,[],[f25])).
% 2.10/0.63  fof(f25,plain,(
% 2.10/0.63    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(flattening,[],[f24])).
% 2.10/0.63  fof(f24,plain,(
% 2.10/0.63    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f7])).
% 2.10/0.63  fof(f7,axiom,(
% 2.10/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 2.10/0.63  fof(f1358,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | ~spl7_72),
% 2.10/0.63    inference(avatar_component_clause,[],[f1357])).
% 2.10/0.63  fof(f1359,plain,(
% 2.10/0.63    spl7_72 | ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_30),
% 2.10/0.63    inference(avatar_split_clause,[],[f1355,f374,f103,f79,f74,f1357])).
% 2.10/0.63  fof(f103,plain,(
% 2.10/0.63    spl7_7 <=> r2_lattice3(sK0,sK1,sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.10/0.63  fof(f374,plain,(
% 2.10/0.63    spl7_30 <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.10/0.63  fof(f1355,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_30)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1354,f75])).
% 2.10/0.63  fof(f1354,plain,(
% 2.10/0.63    ~l1_orders_2(sK0) | r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_3 | ~spl7_7 | ~spl7_30)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1353,f80])).
% 2.10/0.63  fof(f1353,plain,(
% 2.10/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_7 | ~spl7_30)),
% 2.10/0.63    inference(resolution,[],[f413,f104])).
% 2.10/0.63  fof(f104,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK1,sK3) | ~spl7_7),
% 2.10/0.63    inference(avatar_component_clause,[],[f103])).
% 2.10/0.63  fof(f413,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~r2_lattice3(X0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,sK4(sK5(sK0,sK2,sK3)),X1)) ) | ~spl7_30),
% 2.10/0.63    inference(resolution,[],[f375,f64])).
% 2.10/0.63  fof(f64,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f30])).
% 2.10/0.63  fof(f30,plain,(
% 2.10/0.63    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f11])).
% 2.10/0.63  fof(f11,axiom,(
% 2.10/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 2.10/0.63  fof(f375,plain,(
% 2.10/0.63    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_30),
% 2.10/0.63    inference(avatar_component_clause,[],[f374])).
% 2.10/0.63  fof(f976,plain,(
% 2.10/0.63    ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_57),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f975])).
% 2.10/0.63  fof(f975,plain,(
% 2.10/0.63    $false | (~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_57)),
% 2.10/0.63    inference(subsumption_resolution,[],[f974,f116])).
% 2.10/0.63  fof(f116,plain,(
% 2.10/0.63    ~r2_lattice3(sK0,sK1,sK3) | spl7_7),
% 2.10/0.63    inference(avatar_component_clause,[],[f103])).
% 2.10/0.63  fof(f974,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_57)),
% 2.10/0.63    inference(subsumption_resolution,[],[f973,f75])).
% 2.10/0.63  fof(f973,plain,(
% 2.10/0.63    ~l1_orders_2(sK0) | r2_lattice3(sK0,sK1,sK3) | (~spl7_3 | ~spl7_57)),
% 2.10/0.63    inference(subsumption_resolution,[],[f968,f80])).
% 2.10/0.63  fof(f968,plain,(
% 2.10/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK1,sK3) | ~spl7_57),
% 2.10/0.63    inference(resolution,[],[f950,f47])).
% 2.10/0.63  fof(f950,plain,(
% 2.10/0.63    r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~spl7_57),
% 2.10/0.63    inference(avatar_component_clause,[],[f949])).
% 2.10/0.63  fof(f949,plain,(
% 2.10/0.63    spl7_57 <=> r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 2.10/0.63  fof(f963,plain,(
% 2.10/0.63    ~spl7_2 | ~spl7_3 | spl7_7 | spl7_58),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f962])).
% 2.10/0.63  fof(f962,plain,(
% 2.10/0.63    $false | (~spl7_2 | ~spl7_3 | spl7_7 | spl7_58)),
% 2.10/0.63    inference(subsumption_resolution,[],[f961,f116])).
% 2.10/0.63  fof(f961,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | spl7_58)),
% 2.10/0.63    inference(resolution,[],[f953,f86])).
% 2.10/0.63  fof(f86,plain,(
% 2.10/0.63    ( ! [X2] : (m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r2_lattice3(sK0,X2,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(subsumption_resolution,[],[f83,f75])).
% 2.10/0.63  fof(f83,plain,(
% 2.10/0.63    ( ! [X2] : (~l1_orders_2(sK0) | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r2_lattice3(sK0,X2,sK3)) ) | ~spl7_3),
% 2.10/0.63    inference(resolution,[],[f80,f45])).
% 2.10/0.63  fof(f45,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f21])).
% 2.10/0.63  fof(f953,plain,(
% 2.10/0.63    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | spl7_58),
% 2.10/0.63    inference(avatar_component_clause,[],[f952])).
% 2.10/0.63  fof(f952,plain,(
% 2.10/0.63    spl7_58 <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 2.10/0.63  fof(f954,plain,(
% 2.10/0.63    spl7_57 | ~spl7_58 | ~spl7_2 | ~spl7_3 | ~spl7_52),
% 2.10/0.63    inference(avatar_split_clause,[],[f842,f825,f79,f74,f952,f949])).
% 2.10/0.63  fof(f825,plain,(
% 2.10/0.63    spl7_52 <=> r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.10/0.63  fof(f842,plain,(
% 2.10/0.63    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | (~spl7_2 | ~spl7_3 | ~spl7_52)),
% 2.10/0.63    inference(subsumption_resolution,[],[f841,f75])).
% 2.10/0.63  fof(f841,plain,(
% 2.10/0.63    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | (~spl7_3 | ~spl7_52)),
% 2.10/0.63    inference(subsumption_resolution,[],[f835,f80])).
% 2.10/0.63  fof(f835,plain,(
% 2.10/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK5(sK0,sK1,sK3),sK3) | ~spl7_52),
% 2.10/0.63    inference(resolution,[],[f826,f49])).
% 2.10/0.63  fof(f49,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X2,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f22])).
% 2.10/0.63  fof(f22,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f10])).
% 2.10/0.63  fof(f10,axiom,(
% 2.10/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 2.10/0.63  fof(f826,plain,(
% 2.10/0.63    r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | ~spl7_52),
% 2.10/0.63    inference(avatar_component_clause,[],[f825])).
% 2.10/0.63  fof(f827,plain,(
% 2.10/0.63    spl7_52 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_48),
% 2.10/0.63    inference(avatar_split_clause,[],[f812,f721,f192,f79,f74,f70,f825])).
% 2.10/0.63  fof(f70,plain,(
% 2.10/0.63    spl7_1 <=> v4_orders_2(sK0)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.10/0.63  fof(f192,plain,(
% 2.10/0.63    spl7_17 <=> r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.10/0.63  fof(f721,plain,(
% 2.10/0.63    spl7_48 <=> r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.10/0.63  fof(f812,plain,(
% 2.10/0.63    r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_48)),
% 2.10/0.63    inference(resolution,[],[f731,f193])).
% 2.10/0.63  fof(f193,plain,(
% 2.10/0.63    r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~spl7_17),
% 2.10/0.63    inference(avatar_component_clause,[],[f192])).
% 2.10/0.63  fof(f731,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r2_lattice3(sK0,X0,sK3)) ) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_48)),
% 2.10/0.63    inference(subsumption_resolution,[],[f730,f71])).
% 2.10/0.63  fof(f71,plain,(
% 2.10/0.63    v4_orders_2(sK0) | ~spl7_1),
% 2.10/0.63    inference(avatar_component_clause,[],[f70])).
% 2.10/0.63  fof(f730,plain,(
% 2.10/0.63    ( ! [X0] : (~v4_orders_2(sK0) | ~r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r2_lattice3(sK0,X0,sK3)) ) | (~spl7_2 | ~spl7_3 | ~spl7_48)),
% 2.10/0.63    inference(subsumption_resolution,[],[f729,f80])).
% 2.10/0.63  fof(f729,plain,(
% 2.10/0.63    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r2_lattice3(sK0,X0,sK3)) ) | (~spl7_2 | ~spl7_48)),
% 2.10/0.63    inference(subsumption_resolution,[],[f728,f77])).
% 2.10/0.63  fof(f77,plain,(
% 2.10/0.63    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) ) | ~spl7_2),
% 2.10/0.63    inference(resolution,[],[f75,f52])).
% 2.10/0.63  fof(f52,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f23])).
% 2.10/0.63  fof(f23,plain,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f8])).
% 2.10/0.63  fof(f8,axiom,(
% 2.10/0.63    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 2.10/0.63  fof(f728,plain,(
% 2.10/0.63    ( ! [X0] : (~m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r2_lattice3(sK0,X0,sK3)) ) | (~spl7_2 | ~spl7_48)),
% 2.10/0.63    inference(subsumption_resolution,[],[f724,f75])).
% 2.10/0.63  fof(f724,plain,(
% 2.10/0.63    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_lattice3(sK0,X0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r2_lattice3(sK0,X0,sK3)) ) | ~spl7_48),
% 2.10/0.63    inference(resolution,[],[f722,f62])).
% 2.10/0.63  fof(f62,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f29])).
% 2.10/0.63  fof(f29,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 2.10/0.63    inference(flattening,[],[f28])).
% 2.10/0.63  fof(f28,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f9])).
% 2.10/0.63  fof(f9,axiom,(
% 2.10/0.63    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).
% 2.10/0.63  fof(f722,plain,(
% 2.10/0.63    r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3) | ~spl7_48),
% 2.10/0.63    inference(avatar_component_clause,[],[f721])).
% 2.10/0.63  fof(f723,plain,(
% 2.10/0.63    spl7_48 | ~spl7_2 | ~spl7_3 | ~spl7_8 | ~spl7_18),
% 2.10/0.63    inference(avatar_split_clause,[],[f683,f226,f106,f79,f74,f721])).
% 2.10/0.63  fof(f226,plain,(
% 2.10/0.63    spl7_18 <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.10/0.63  fof(f683,plain,(
% 2.10/0.63    r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3) | (~spl7_2 | ~spl7_3 | ~spl7_8 | ~spl7_18)),
% 2.10/0.63    inference(subsumption_resolution,[],[f682,f80])).
% 2.10/0.63  fof(f682,plain,(
% 2.10/0.63    r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_2 | ~spl7_8 | ~spl7_18)),
% 2.10/0.63    inference(resolution,[],[f555,f107])).
% 2.10/0.63  fof(f107,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | ~spl7_8),
% 2.10/0.63    inference(avatar_component_clause,[],[f106])).
% 2.10/0.63  fof(f555,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_lattice3(sK0,sK2,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_2 | ~spl7_18)),
% 2.10/0.63    inference(resolution,[],[f227,f139])).
% 2.10/0.63  fof(f139,plain,(
% 2.10/0.63    ( ! [X6,X8,X7] : (~r2_hidden(k1_yellow_0(sK0,X7),X8) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,k1_yellow_0(sK0,X7),X6) | ~r2_lattice3(sK0,X8,X6)) ) | ~spl7_2),
% 2.10/0.63    inference(subsumption_resolution,[],[f134,f75])).
% 2.10/0.63  fof(f134,plain,(
% 2.10/0.63    ( ! [X6,X8,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_hidden(k1_yellow_0(sK0,X7),X8) | r1_orders_2(sK0,k1_yellow_0(sK0,X7),X6) | ~r2_lattice3(sK0,X8,X6)) ) | ~spl7_2),
% 2.10/0.63    inference(resolution,[],[f77,f44])).
% 2.10/0.63  fof(f44,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f21])).
% 2.10/0.63  fof(f227,plain,(
% 2.10/0.63    r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | ~spl7_18),
% 2.10/0.63    inference(avatar_component_clause,[],[f226])).
% 2.10/0.63  fof(f550,plain,(
% 2.10/0.63    ~spl7_7 | ~spl7_8),
% 2.10/0.63    inference(avatar_split_clause,[],[f109,f106,f103])).
% 2.10/0.63  fof(f109,plain,(
% 2.10/0.63    ~r2_lattice3(sK0,sK1,sK3) | ~spl7_8),
% 2.10/0.63    inference(subsumption_resolution,[],[f36,f107])).
% 2.10/0.63  fof(f36,plain,(
% 2.10/0.63    ~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,plain,(
% 2.10/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.10/0.63    inference(flattening,[],[f18])).
% 2.10/0.63  fof(f18,plain,(
% 2.10/0.63    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f17])).
% 2.10/0.63  fof(f17,plain,(
% 2.10/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.10/0.63    inference(pure_predicate_removal,[],[f16])).
% 2.10/0.63  fof(f16,plain,(
% 2.10/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.10/0.63    inference(pure_predicate_removal,[],[f14])).
% 2.10/0.63  fof(f14,plain,(
% 2.10/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.10/0.63    inference(rectify,[],[f13])).
% 2.10/0.63  fof(f13,negated_conjecture,(
% 2.10/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.10/0.63    inference(negated_conjecture,[],[f12])).
% 2.10/0.63  fof(f12,conjecture,(
% 2.10/0.63    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).
% 2.10/0.63  fof(f476,plain,(
% 2.10/0.63    spl7_34 | ~spl7_2 | ~spl7_32),
% 2.10/0.63    inference(avatar_split_clause,[],[f454,f416,f74,f474])).
% 2.10/0.63  fof(f454,plain,(
% 2.10/0.63    m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_2 | ~spl7_32)),
% 2.10/0.63    inference(superposition,[],[f77,f417])).
% 2.10/0.63  fof(f418,plain,(
% 2.10/0.63    spl7_32 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.10/0.63    inference(avatar_split_clause,[],[f402,f106,f79,f74,f416])).
% 2.10/0.63  fof(f402,plain,(
% 2.10/0.63    sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.10/0.63    inference(subsumption_resolution,[],[f333,f240])).
% 2.10/0.63  fof(f333,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f332])).
% 2.10/0.63  fof(f332,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r2_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f152,f87])).
% 2.10/0.63  fof(f87,plain,(
% 2.10/0.63    ( ! [X3] : (r2_hidden(sK5(sK0,X3,sK3),X3) | r2_lattice3(sK0,X3,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(subsumption_resolution,[],[f84,f75])).
% 2.10/0.63  fof(f84,plain,(
% 2.10/0.63    ( ! [X3] : (~l1_orders_2(sK0) | r2_hidden(sK5(sK0,X3,sK3),X3) | r2_lattice3(sK0,X3,sK3)) ) | ~spl7_3),
% 2.10/0.63    inference(resolution,[],[f80,f46])).
% 2.10/0.63  fof(f46,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f21])).
% 2.10/0.63  fof(f152,plain,(
% 2.10/0.63    ( ! [X0] : (~r2_hidden(sK5(sK0,X0,sK3),sK2) | r2_lattice3(sK0,X0,sK3) | sK5(sK0,X0,sK3) = k1_yellow_0(sK0,sK4(sK5(sK0,X0,sK3)))) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f86,f34])).
% 2.10/0.63  fof(f34,plain,(
% 2.10/0.63    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | k1_yellow_0(sK0,sK4(X4)) = X4) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f376,plain,(
% 2.10/0.63    spl7_30 | ~spl7_28),
% 2.10/0.63    inference(avatar_split_clause,[],[f370,f336,f374])).
% 2.10/0.63  fof(f336,plain,(
% 2.10/0.63    spl7_28 <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.10/0.63  fof(f370,plain,(
% 2.10/0.63    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_28),
% 2.10/0.63    inference(resolution,[],[f337,f61])).
% 2.10/0.63  fof(f61,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f27])).
% 2.10/0.63  fof(f27,plain,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f15])).
% 2.10/0.63  fof(f15,plain,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.10/0.63    inference(unused_predicate_definition_removal,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.63  fof(f337,plain,(
% 2.10/0.63    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_28),
% 2.10/0.63    inference(avatar_component_clause,[],[f336])).
% 2.10/0.63  fof(f338,plain,(
% 2.10/0.63    spl7_28 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.10/0.63    inference(avatar_split_clause,[],[f316,f106,f79,f74,f336])).
% 2.10/0.63  fof(f316,plain,(
% 2.10/0.63    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.10/0.63    inference(subsumption_resolution,[],[f294,f240])).
% 2.10/0.63  fof(f294,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f293])).
% 2.10/0.63  fof(f293,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | r2_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f153,f87])).
% 2.10/0.63  fof(f153,plain,(
% 2.10/0.63    ( ! [X1] : (~r2_hidden(sK5(sK0,X1,sK3),sK2) | r2_lattice3(sK0,X1,sK3) | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1))) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f86,f32])).
% 2.10/0.63  fof(f32,plain,(
% 2.10/0.63    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f299,plain,(
% 2.10/0.63    spl7_26 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.10/0.63    inference(avatar_split_clause,[],[f292,f106,f79,f74,f297])).
% 2.10/0.63  fof(f292,plain,(
% 2.10/0.63    r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.10/0.63    inference(subsumption_resolution,[],[f291,f240])).
% 2.10/0.63  fof(f291,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f290])).
% 2.10/0.63  fof(f290,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | r1_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r2_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f154,f87])).
% 2.10/0.63  fof(f154,plain,(
% 2.10/0.63    ( ! [X2] : (~r2_hidden(sK5(sK0,X2,sK3),sK2) | r2_lattice3(sK0,X2,sK3) | r1_yellow_0(sK0,sK4(sK5(sK0,X2,sK3)))) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f86,f33])).
% 2.10/0.63  fof(f33,plain,(
% 2.10/0.63    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | r1_yellow_0(sK0,sK4(X4))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f228,plain,(
% 2.10/0.63    spl7_18 | spl7_16 | ~spl7_2 | ~spl7_3 | spl7_7),
% 2.10/0.63    inference(avatar_split_clause,[],[f177,f103,f79,f74,f187,f226])).
% 2.10/0.63  fof(f187,plain,(
% 2.10/0.63    spl7_16 <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.10/0.63  fof(f177,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f176,f60])).
% 2.10/0.63  fof(f60,plain,(
% 2.10/0.63    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f5])).
% 2.10/0.63  fof(f5,axiom,(
% 2.10/0.63    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 2.10/0.63  fof(f176,plain,(
% 2.10/0.63    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f174,f116])).
% 2.10/0.63  fof(f174,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f151,f38])).
% 2.10/0.63  fof(f38,plain,(
% 2.10/0.63    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~v1_finset_1(X3) | k1_xboole_0 = X3 | r2_hidden(k1_yellow_0(sK0,X3),sK2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f151,plain,(
% 2.10/0.63    ( ! [X0] : (m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0)) | r2_lattice3(sK0,X0,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f87,f58])).
% 2.10/0.63  fof(f58,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f26])).
% 2.10/0.63  fof(f26,plain,(
% 2.10/0.63    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f3])).
% 2.10/0.63  fof(f3,axiom,(
% 2.10/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 2.10/0.63  fof(f204,plain,(
% 2.10/0.63    ~spl7_16),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f203])).
% 2.10/0.63  fof(f203,plain,(
% 2.10/0.63    $false | ~spl7_16),
% 2.10/0.63    inference(subsumption_resolution,[],[f197,f59])).
% 2.10/0.63  fof(f59,plain,(
% 2.10/0.63    v1_xboole_0(k1_xboole_0)),
% 2.10/0.63    inference(cnf_transformation,[],[f1])).
% 2.10/0.63  fof(f1,axiom,(
% 2.10/0.63    v1_xboole_0(k1_xboole_0)),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.10/0.63  fof(f197,plain,(
% 2.10/0.63    ~v1_xboole_0(k1_xboole_0) | ~spl7_16),
% 2.10/0.63    inference(superposition,[],[f66,f188])).
% 2.10/0.63  fof(f188,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | ~spl7_16),
% 2.10/0.63    inference(avatar_component_clause,[],[f187])).
% 2.10/0.63  fof(f66,plain,(
% 2.10/0.63    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f2])).
% 2.10/0.63  fof(f2,axiom,(
% 2.10/0.63    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.10/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.10/0.63  fof(f194,plain,(
% 2.10/0.63    spl7_17 | ~spl7_2 | ~spl7_15),
% 2.10/0.63    inference(avatar_split_clause,[],[f190,f184,f74,f192])).
% 2.10/0.63  fof(f184,plain,(
% 2.10/0.63    spl7_15 <=> r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.10/0.63  fof(f190,plain,(
% 2.10/0.63    r2_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | (~spl7_2 | ~spl7_15)),
% 2.10/0.63    inference(resolution,[],[f185,f138])).
% 2.10/0.63  fof(f138,plain,(
% 2.10/0.63    ( ! [X2] : (~r1_yellow_0(sK0,X2) | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))) ) | ~spl7_2),
% 2.10/0.63    inference(subsumption_resolution,[],[f130,f75])).
% 2.10/0.63  fof(f130,plain,(
% 2.10/0.63    ( ! [X2] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X2) | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))) ) | ~spl7_2),
% 2.10/0.63    inference(resolution,[],[f77,f67])).
% 2.10/0.63  fof(f67,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))) )),
% 2.10/0.63    inference(equality_resolution,[],[f57])).
% 2.10/0.63  fof(f57,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2) )),
% 2.10/0.63    inference(cnf_transformation,[],[f25])).
% 2.10/0.63  fof(f185,plain,(
% 2.10/0.63    r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~spl7_15),
% 2.10/0.63    inference(avatar_component_clause,[],[f184])).
% 2.10/0.63  fof(f189,plain,(
% 2.10/0.63    spl7_15 | spl7_16 | ~spl7_2 | ~spl7_3 | spl7_7),
% 2.10/0.63    inference(avatar_split_clause,[],[f179,f103,f79,f74,f187,f184])).
% 2.10/0.63  fof(f179,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f178,f60])).
% 2.10/0.63  fof(f178,plain,(
% 2.10/0.63    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f175,f116])).
% 2.10/0.63  fof(f175,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r1_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.10/0.63    inference(resolution,[],[f151,f39])).
% 2.10/0.63  fof(f39,plain,(
% 2.10/0.63    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(sK1)) | ~v1_finset_1(X6) | k1_xboole_0 = X6 | r1_yellow_0(sK0,X6)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f108,plain,(
% 2.10/0.63    spl7_7 | spl7_8),
% 2.10/0.63    inference(avatar_split_clause,[],[f35,f106,f103])).
% 2.10/0.63  fof(f35,plain,(
% 2.10/0.63    r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f81,plain,(
% 2.10/0.63    spl7_3),
% 2.10/0.63    inference(avatar_split_clause,[],[f37,f79])).
% 2.10/0.63  fof(f37,plain,(
% 2.10/0.63    m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f76,plain,(
% 2.10/0.63    spl7_2),
% 2.10/0.63    inference(avatar_split_clause,[],[f43,f74])).
% 2.10/0.63  fof(f43,plain,(
% 2.10/0.63    l1_orders_2(sK0)),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f72,plain,(
% 2.10/0.63    spl7_1),
% 2.10/0.63    inference(avatar_split_clause,[],[f42,f70])).
% 2.10/0.63  fof(f42,plain,(
% 2.10/0.63    v4_orders_2(sK0)),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  % SZS output end Proof for theBenchmark
% 2.10/0.63  % (26590)------------------------------
% 2.10/0.63  % (26590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.63  % (26590)Termination reason: Refutation
% 2.10/0.63  
% 2.10/0.63  % (26590)Memory used [KB]: 7036
% 2.10/0.63  % (26590)Time elapsed: 0.215 s
% 2.10/0.63  % (26590)------------------------------
% 2.10/0.63  % (26590)------------------------------
% 2.10/0.64  % (26589)Success in time 0.274 s
%------------------------------------------------------------------------------
