%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1677+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:19 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 531 expanded)
%              Number of leaves         :   32 ( 186 expanded)
%              Depth                    :   13
%              Number of atoms          :  898 (3203 expanded)
%              Number of equality atoms :   43 ( 263 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f84,f111,f173,f231,f301,f314,f358,f430,f496,f500,f1405,f1438,f1450,f1487,f2207,f2238,f2360,f3637,f3648,f4592])).

fof(f4592,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_87 ),
    inference(avatar_contradiction_clause,[],[f4591])).

fof(f4591,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_87 ),
    inference(subsumption_resolution,[],[f4590,f119])).

fof(f119,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_7
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f4590,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_87 ),
    inference(resolution,[],[f4584,f89])).

fof(f89,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f86,f78])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f86,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f83,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f4584,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_87 ),
    inference(avatar_component_clause,[],[f2000])).

fof(f2000,plain,
    ( spl7_87
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f3648,plain,
    ( spl7_107
    | ~ spl7_2
    | ~ spl7_27
    | ~ spl7_87 ),
    inference(avatar_split_clause,[],[f3640,f2000,f299,f77,f2565])).

fof(f2565,plain,
    ( spl7_107
  <=> r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f299,plain,
    ( spl7_27
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f3640,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3))
    | ~ spl7_2
    | ~ spl7_27
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f3639,f78])).

fof(f3639,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3))
    | ~ spl7_2
    | ~ spl7_27
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f3638,f2001])).

fof(f2001,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_87 ),
    inference(avatar_component_clause,[],[f2000])).

fof(f3638,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3))
    | ~ spl7_2
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f2321,f80])).

fof(f80,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f2321,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3))
    | ~ spl7_27 ),
    inference(resolution,[],[f300,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f300,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f299])).

fof(f3637,plain,
    ( spl7_90
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_87
    | ~ spl7_102
    | ~ spl7_107 ),
    inference(avatar_split_clause,[],[f3604,f2565,f2358,f2000,f82,f77,f73,f2080])).

fof(f2080,plain,
    ( spl7_90
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f73,plain,
    ( spl7_1
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2358,plain,
    ( spl7_102
  <=> r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f3604,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_87
    | ~ spl7_102
    | ~ spl7_107 ),
    inference(subsumption_resolution,[],[f3600,f2001])).

fof(f3600,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_102
    | ~ spl7_107 ),
    inference(resolution,[],[f2415,f2566])).

fof(f2566,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK5(sK0,sK1,sK3))
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f2565])).

fof(f2415,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f2414,f74])).

fof(f74,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f2414,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f2413,f80])).

fof(f2413,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f2412,f83])).

fof(f2412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_2
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f2405,f78])).

fof(f2405,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),X0)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_102 ),
    inference(resolution,[],[f2359,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f2359,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f2360,plain,
    ( spl7_102
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f2354,f356,f109,f82,f77,f2358])).

fof(f109,plain,
    ( spl7_8
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f356,plain,
    ( spl7_29
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f2354,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f2350,f83])).

fof(f2350,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(resolution,[],[f2257,f110])).

fof(f110,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f2257,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_29 ),
    inference(resolution,[],[f357,f144])).

fof(f144,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(k2_yellow_0(sK0,X7),X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7))
        | ~ r1_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f139,f78])).

fof(f139,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(k2_yellow_0(sK0,X7),X8)
        | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7))
        | ~ r1_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f357,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f356])).

fof(f2238,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_90 ),
    inference(avatar_contradiction_clause,[],[f2237])).

fof(f2237,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f2236,f119])).

fof(f2236,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f2235,f78])).

fof(f2235,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f2231,f83])).

fof(f2231,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_90 ),
    inference(resolution,[],[f2081,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2081,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f2080])).

fof(f2207,plain,
    ( spl7_90
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_87 ),
    inference(avatar_split_clause,[],[f2188,f2000,f229,f171,f82,f77,f2080])).

fof(f171,plain,
    ( spl7_12
  <=> r1_lattice3(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f229,plain,
    ( spl7_19
  <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f2188,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f2187,f78])).

fof(f2187,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_87 ),
    inference(subsumption_resolution,[],[f2186,f2001])).

fof(f2186,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f2176,f83])).

fof(f2176,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(resolution,[],[f490,f172])).

fof(f172,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f490,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(X2,k1_xboole_0,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | r1_orders_2(X2,X3,sK5(sK0,sK1,sK3)) )
    | ~ spl7_19 ),
    inference(superposition,[],[f66,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f1487,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f112,f109,f106])).

fof(f112,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f37,f110])).

fof(f37,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
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
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,negated_conjecture,(
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
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X3)
                      <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f1450,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_75 ),
    inference(avatar_contradiction_clause,[],[f1449])).

fof(f1449,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f1448,f243])).

fof(f243,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1448,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f1447,f78])).

fof(f1447,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f1443,f83])).

fof(f1443,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_75 ),
    inference(resolution,[],[f1437,f48])).

fof(f1437,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1436,plain,
    ( spl7_75
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1438,plain,
    ( spl7_75
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_36
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1417,f877,f494,f312,f82,f77,f1436])).

fof(f312,plain,
    ( spl7_28
  <=> r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f494,plain,
    ( spl7_36
  <=> sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f877,plain,
    ( spl7_58
  <=> r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f1417,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_36
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1406,f83])).

fof(f1406,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_28
    | ~ spl7_36
    | ~ spl7_58 ),
    inference(resolution,[],[f878,f518])).

fof(f518,plain,
    ( ! [X8] :
        ( ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_orders_2(sK0,X8,sK5(sK0,sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_28
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f517,f313])).

fof(f313,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f312])).

fof(f517,plain,
    ( ! [X8] :
        ( ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X8)
        | r1_orders_2(sK0,X8,sK5(sK0,sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f516,f78])).

fof(f516,plain,
    ( ! [X8] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X8)
        | r1_orders_2(sK0,X8,sK5(sK0,sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f514,f501])).

fof(f501,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_36 ),
    inference(superposition,[],[f80,f495])).

fof(f495,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f494])).

fof(f514,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X8)
        | r1_orders_2(sK0,X8,sK5(sK0,sK2,sK3)) )
    | ~ spl7_36 ),
    inference(superposition,[],[f71,f495])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f878,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f877])).

fof(f1405,plain,
    ( spl7_58
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1400,f498,f106,f82,f77,f877])).

fof(f498,plain,
    ( spl7_37
  <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f1400,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1399,f78])).

fof(f1399,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1398,f83])).

fof(f1398,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_7
    | ~ spl7_37 ),
    inference(resolution,[],[f523,f107])).

fof(f107,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f523,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(X2,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | r1_lattice3(X2,sK4(sK5(sK0,sK2,sK3)),X3) )
    | ~ spl7_37 ),
    inference(resolution,[],[f499,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f499,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f498])).

fof(f500,plain,
    ( spl7_37
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f483,f428,f498])).

fof(f428,plain,
    ( spl7_32
  <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f483,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_32 ),
    inference(resolution,[],[f429,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f429,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f428])).

fof(f496,plain,
    ( spl7_36
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f472,f109,f82,f77,f494])).

fof(f472,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f334,f243])).

fof(f334,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f160,f90])).

fof(f90,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f87,f78])).

fof(f87,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | sK5(sK0,X0,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,X0,sK3))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k2_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f430,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f414,f109,f82,f77,f428])).

fof(f414,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f297,f243])).

fof(f297,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f161,f90])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK0,X1,sK3),sK2)
        | r1_lattice3(sK0,X1,sK3)
        | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f358,plain,
    ( spl7_29
    | spl7_19
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f315,f109,f82,f77,f229,f356])).

fof(f315,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f233,f112])).

fof(f233,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f205,f59])).

fof(f59,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f205,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f203,f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f203,plain,
    ( ! [X7] :
        ( m1_subset_1(k1_tarski(sK5(sK0,X7,sK3)),k1_zfmisc_1(X7))
        | r1_lattice3(sK0,X7,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f157,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f157,plain,
    ( ! [X1] :
        ( r1_tarski(k1_tarski(sK5(sK0,X1,sK3)),X1)
        | r1_lattice3(sK0,X1,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f314,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f302,f109,f82,f77,f312])).

fof(f302,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f295,f243])).

fof(f295,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f162,f90])).

fof(f162,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK0,X2,sK3),sK2)
        | r1_lattice3(sK0,X2,sK3)
        | r2_yellow_0(sK0,sK4(sK5(sK0,X2,sK3))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | r2_yellow_0(sK0,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f301,plain,
    ( spl7_27
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f281,f226,f77,f299])).

fof(f226,plain,
    ( spl7_18
  <=> r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f281,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f227,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f135,f78])).

fof(f135,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f227,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f231,plain,
    ( spl7_18
    | spl7_19
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f210,f106,f82,f77,f229,f226])).

fof(f210,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f209,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f206,f119])).

fof(f206,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f203,f40])).

fof(f40,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | r2_yellow_0(sK0,X6) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f173,plain,
    ( spl7_12
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f159,f82,f77,f171])).

fof(f159,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f156,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f90,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f111,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f36,f109,f106])).

fof(f36,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f44,f77])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
