%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:17 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 480 expanded)
%              Number of leaves         :   32 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  838 (2876 expanded)
%              Number of equality atoms :   43 ( 242 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1962,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f84,f111,f201,f206,f216,f244,f329,f364,f415,f466,f548,f630,f800,f1414,f1652,f1740,f1767,f1913,f1944,f1955])).

fof(f1955,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_89 ),
    inference(avatar_contradiction_clause,[],[f1954])).

fof(f1954,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f1953,f260])).

fof(f260,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_8
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1953,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f1952,f78])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1952,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f1946,f83])).

fof(f83,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1946,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_89 ),
    inference(resolution,[],[f1943,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f1943,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f1942])).

fof(f1942,plain,
    ( spl7_89
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f1944,plain,
    ( spl7_89
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1924,f762,f546,f464,f327,f82,f77,f1942])).

fof(f327,plain,
    ( spl7_26
  <=> r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f464,plain,
    ( spl7_32
  <=> sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f546,plain,
    ( spl7_34
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f762,plain,
    ( spl7_45
  <=> r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1924,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f1914,f83])).

fof(f1914,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34
    | ~ spl7_45 ),
    inference(resolution,[],[f763,f1788])).

fof(f1788,plain,
    ( ! [X6] :
        ( ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_26
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f612,f328])).

fof(f328,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f327])).

fof(f612,plain,
    ( ! [X6] :
        ( ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6)
        | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3)) )
    | ~ spl7_2
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f611,f78])).

fof(f611,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6)
        | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3)) )
    | ~ spl7_32
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f609,f547])).

fof(f547,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f546])).

fof(f609,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6)
        | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3)) )
    | ~ spl7_32 ),
    inference(superposition,[],[f71,f465])).

fof(f465,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f464])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f763,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f762])).

fof(f1913,plain,
    ( spl7_45
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f1816,f413,f106,f82,f77,f762])).

fof(f106,plain,
    ( spl7_7
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f413,plain,
    ( spl7_30
  <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1816,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1815,f78])).

fof(f1815,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1806,f83])).

fof(f1806,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_7
    | ~ spl7_30 ),
    inference(resolution,[],[f107,f454])).

fof(f454,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(X2,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | r1_lattice3(X2,sK4(sK5(sK0,sK2,sK3)),X3) )
    | ~ spl7_30 ),
    inference(resolution,[],[f414,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f414,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f413])).

fof(f107,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1767,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_82 ),
    inference(avatar_contradiction_clause,[],[f1766])).

fof(f1766,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1765,f123])).

fof(f123,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1765,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1764,f78])).

fof(f1764,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1761,f83])).

fof(f1761,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_82 ),
    inference(resolution,[],[f1739,f50])).

fof(f1739,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f1738])).

fof(f1738,plain,
    ( spl7_82
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f1740,plain,
    ( spl7_82
    | ~ spl7_64
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1673,f1650,f82,f77,f1394,f1738])).

fof(f1394,plain,
    ( spl7_64
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f1650,plain,
    ( spl7_77
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f1673,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f1672,f78])).

fof(f1672,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f1665,f83])).

fof(f1665,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_77 ),
    inference(resolution,[],[f1651,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f1651,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1652,plain,
    ( spl7_77
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f1639,f798,f204,f82,f77,f73,f1650])).

fof(f73,plain,
    ( spl7_1
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f204,plain,
    ( spl7_17
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f798,plain,
    ( spl7_48
  <=> r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f1639,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f1636,f83])).

fof(f1636,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_48 ),
    inference(resolution,[],[f238,f799])).

fof(f799,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f798])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f237,f74])).

fof(f74,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0) )
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f236,f80])).

fof(f80,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0) )
    | ~ spl7_2
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f230,f78])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0) )
    | ~ spl7_17 ),
    inference(resolution,[],[f205,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X3,X2)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_lattice3(X0,X1,X3)
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_lattice3(X0,X1,X3)
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X2) )
               => r1_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_0)).

fof(f205,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1414,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_64 ),
    inference(avatar_contradiction_clause,[],[f1413])).

fof(f1413,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | spl7_64 ),
    inference(subsumption_resolution,[],[f1412,f123])).

fof(f1412,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_64 ),
    inference(resolution,[],[f1395,f89])).

fof(f89,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f86,f78])).

fof(f86,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1395,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_64 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f800,plain,
    ( spl7_48
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f796,f242,f109,f82,f77,f798])).

fof(f242,plain,
    ( spl7_18
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f796,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f795,f83])).

fof(f795,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(resolution,[],[f635,f110])).

fof(f110,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f243,f146])).

fof(f146,plain,
    ( ! [X6,X8,X7] :
        ( ~ r2_hidden(k2_yellow_0(sK0,X7),X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7))
        | ~ r1_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f141,f78])).

fof(f141,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(k2_yellow_0(sK0,X7),X8)
        | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7))
        | ~ r1_lattice3(sK0,X8,X6) )
    | ~ spl7_2 ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f243,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f630,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f112,f109,f106])).

fof(f112,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f39,f110])).

fof(f39,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
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

fof(f548,plain,
    ( spl7_34
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f525,f464,f77,f546])).

fof(f525,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(superposition,[],[f80,f465])).

fof(f466,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f444,f109,f82,f77,f464])).

fof(f444,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f439,f260])).

fof(f439,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f438])).

fof(f438,plain,
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
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | sK5(sK0,X0,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,X0,sK3))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k2_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f415,plain,
    ( spl7_30
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f400,f362,f413])).

fof(f362,plain,
    ( spl7_28
  <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f400,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f363,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f363,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f364,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f351,f109,f82,f77,f362])).

fof(f351,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f346,f260])).

fof(f346,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
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
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f329,plain,
    ( spl7_26
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f325,f109,f82,f77,f327])).

fof(f325,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f324,f260])).

fof(f324,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,
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
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | r2_yellow_0(sK0,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f244,plain,
    ( spl7_18
    | spl7_16
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f185,f106,f82,f77,f199,f242])).

fof(f199,plain,
    ( spl7_16
  <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f185,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f184,f60])).

fof(f60,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f184,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f182,f123])).

fof(f182,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f158,f41])).

fof(f41,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f158,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0))
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f216,plain,(
    ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f209,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_16 ),
    inference(superposition,[],[f67,f200])).

fof(f200,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f206,plain,
    ( spl7_17
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f202,f196,f77,f204])).

fof(f196,plain,
    ( spl7_15
  <=> r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f202,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(resolution,[],[f197,f145])).

fof(f145,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f137,f78])).

fof(f137,plain,
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
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f197,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( spl7_15
    | spl7_16
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f187,f106,f82,f77,f199,f196])).

fof(f187,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f186,f60])).

fof(f186,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f183,f123])).

fof(f183,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f158,f42])).

fof(f42,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | r2_yellow_0(sK0,X6) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f111,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f38,f109,f106])).

fof(f38,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f45,f73])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (24616)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (24624)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (24610)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (24622)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (24619)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (24614)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (24609)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (24612)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (24620)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (24611)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (24625)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (24608)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (24623)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (24626)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (24613)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (24628)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (24621)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (24617)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (24618)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (24627)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (24615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 2.09/0.64  % (24608)Refutation found. Thanks to Tanya!
% 2.09/0.64  % SZS status Theorem for theBenchmark
% 2.09/0.64  % SZS output start Proof for theBenchmark
% 2.09/0.64  fof(f1962,plain,(
% 2.09/0.64    $false),
% 2.09/0.64    inference(avatar_sat_refutation,[],[f75,f79,f84,f111,f201,f206,f216,f244,f329,f364,f415,f466,f548,f630,f800,f1414,f1652,f1740,f1767,f1913,f1944,f1955])).
% 2.09/0.64  fof(f1955,plain,(
% 2.09/0.64    ~spl7_2 | ~spl7_3 | spl7_8 | ~spl7_89),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f1954])).
% 2.09/0.64  fof(f1954,plain,(
% 2.09/0.64    $false | (~spl7_2 | ~spl7_3 | spl7_8 | ~spl7_89)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1953,f260])).
% 2.09/0.64  fof(f260,plain,(
% 2.09/0.64    ~r1_lattice3(sK0,sK2,sK3) | spl7_8),
% 2.09/0.64    inference(avatar_component_clause,[],[f109])).
% 2.09/0.64  fof(f109,plain,(
% 2.09/0.64    spl7_8 <=> r1_lattice3(sK0,sK2,sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.09/0.64  fof(f1953,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_89)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1952,f78])).
% 2.09/0.64  fof(f78,plain,(
% 2.09/0.64    l1_orders_2(sK0) | ~spl7_2),
% 2.09/0.64    inference(avatar_component_clause,[],[f77])).
% 2.09/0.64  fof(f77,plain,(
% 2.09/0.64    spl7_2 <=> l1_orders_2(sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.09/0.64  fof(f1952,plain,(
% 2.09/0.64    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_89)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1946,f83])).
% 2.09/0.64  fof(f83,plain,(
% 2.09/0.64    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_3),
% 2.09/0.64    inference(avatar_component_clause,[],[f82])).
% 2.09/0.64  fof(f82,plain,(
% 2.09/0.64    spl7_3 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.09/0.64  fof(f1946,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | ~spl7_89),
% 2.09/0.64    inference(resolution,[],[f1943,f50])).
% 2.09/0.64  fof(f50,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f22])).
% 2.09/0.64  fof(f22,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(flattening,[],[f21])).
% 2.09/0.64  fof(f21,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f7])).
% 2.09/0.64  fof(f7,axiom,(
% 2.09/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 2.09/0.64  fof(f1943,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | ~spl7_89),
% 2.09/0.64    inference(avatar_component_clause,[],[f1942])).
% 2.09/0.64  fof(f1942,plain,(
% 2.09/0.64    spl7_89 <=> r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 2.09/0.64  fof(f1944,plain,(
% 2.09/0.64    spl7_89 | ~spl7_2 | ~spl7_3 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_45),
% 2.09/0.64    inference(avatar_split_clause,[],[f1924,f762,f546,f464,f327,f82,f77,f1942])).
% 2.09/0.64  fof(f327,plain,(
% 2.09/0.64    spl7_26 <=> r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.09/0.64  fof(f464,plain,(
% 2.09/0.64    spl7_32 <=> sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.09/0.64  fof(f546,plain,(
% 2.09/0.64    spl7_34 <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 2.09/0.64  fof(f762,plain,(
% 2.09/0.64    spl7_45 <=> r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.09/0.64  fof(f1924,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | (~spl7_2 | ~spl7_3 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_45)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1914,f83])).
% 2.09/0.64  fof(f1914,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | (~spl7_2 | ~spl7_26 | ~spl7_32 | ~spl7_34 | ~spl7_45)),
% 2.09/0.64    inference(resolution,[],[f763,f1788])).
% 2.09/0.64  fof(f1788,plain,(
% 2.09/0.64    ( ! [X6] : (~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3))) ) | (~spl7_2 | ~spl7_26 | ~spl7_32 | ~spl7_34)),
% 2.09/0.64    inference(subsumption_resolution,[],[f612,f328])).
% 2.09/0.64  fof(f328,plain,(
% 2.09/0.64    r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_26),
% 2.09/0.64    inference(avatar_component_clause,[],[f327])).
% 2.09/0.64  fof(f612,plain,(
% 2.09/0.64    ( ! [X6] : (~r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6) | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3))) ) | (~spl7_2 | ~spl7_32 | ~spl7_34)),
% 2.09/0.64    inference(subsumption_resolution,[],[f611,f78])).
% 2.09/0.64  fof(f611,plain,(
% 2.09/0.64    ( ! [X6] : (~l1_orders_2(sK0) | ~r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6) | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3))) ) | (~spl7_32 | ~spl7_34)),
% 2.09/0.64    inference(subsumption_resolution,[],[f609,f547])).
% 2.09/0.64  fof(f547,plain,(
% 2.09/0.64    m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_34),
% 2.09/0.64    inference(avatar_component_clause,[],[f546])).
% 2.09/0.64  fof(f609,plain,(
% 2.09/0.64    ( ! [X6] : (~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X6) | r1_orders_2(sK0,X6,sK5(sK0,sK2,sK3))) ) | ~spl7_32),
% 2.09/0.64    inference(superposition,[],[f71,f465])).
% 2.09/0.64  fof(f465,plain,(
% 2.09/0.64    sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_32),
% 2.09/0.64    inference(avatar_component_clause,[],[f464])).
% 2.09/0.64  fof(f71,plain,(
% 2.09/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,k2_yellow_0(X0,X1))) )),
% 2.09/0.64    inference(equality_resolution,[],[f55])).
% 2.09/0.64  fof(f55,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,X2) | k2_yellow_0(X0,X1) != X2) )),
% 2.09/0.64    inference(cnf_transformation,[],[f25])).
% 2.09/0.64  fof(f25,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(flattening,[],[f24])).
% 2.09/0.64  fof(f24,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f8])).
% 2.09/0.64  fof(f8,axiom,(
% 2.09/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 2.09/0.64  fof(f763,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | ~spl7_45),
% 2.09/0.64    inference(avatar_component_clause,[],[f762])).
% 2.09/0.64  fof(f1913,plain,(
% 2.09/0.64    spl7_45 | ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_30),
% 2.09/0.64    inference(avatar_split_clause,[],[f1816,f413,f106,f82,f77,f762])).
% 2.09/0.64  fof(f106,plain,(
% 2.09/0.64    spl7_7 <=> r1_lattice3(sK0,sK1,sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.09/0.64  fof(f413,plain,(
% 2.09/0.64    spl7_30 <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 2.09/0.64  fof(f1816,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_30)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1815,f78])).
% 2.09/0.64  fof(f1815,plain,(
% 2.09/0.64    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_3 | ~spl7_7 | ~spl7_30)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1806,f83])).
% 2.09/0.64  fof(f1806,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_7 | ~spl7_30)),
% 2.09/0.64    inference(resolution,[],[f107,f454])).
% 2.09/0.64  fof(f454,plain,(
% 2.09/0.64    ( ! [X2,X3] : (~r1_lattice3(X2,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | r1_lattice3(X2,sK4(sK5(sK0,sK2,sK3)),X3)) ) | ~spl7_30),
% 2.09/0.64    inference(resolution,[],[f414,f69])).
% 2.09/0.64  fof(f69,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f33])).
% 2.09/0.64  fof(f33,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f12])).
% 2.09/0.64  fof(f12,axiom,(
% 2.09/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 2.09/0.64  fof(f414,plain,(
% 2.09/0.64    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_30),
% 2.09/0.64    inference(avatar_component_clause,[],[f413])).
% 2.09/0.64  fof(f107,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK1,sK3) | ~spl7_7),
% 2.09/0.64    inference(avatar_component_clause,[],[f106])).
% 2.09/0.64  fof(f1767,plain,(
% 2.09/0.64    ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_82),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f1766])).
% 2.09/0.64  fof(f1766,plain,(
% 2.09/0.64    $false | (~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_82)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1765,f123])).
% 2.09/0.64  fof(f123,plain,(
% 2.09/0.64    ~r1_lattice3(sK0,sK1,sK3) | spl7_7),
% 2.09/0.64    inference(avatar_component_clause,[],[f106])).
% 2.09/0.64  fof(f1765,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_82)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1764,f78])).
% 2.09/0.64  fof(f1764,plain,(
% 2.09/0.64    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK1,sK3) | (~spl7_3 | ~spl7_82)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1761,f83])).
% 2.09/0.64  fof(f1761,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK1,sK3) | ~spl7_82),
% 2.09/0.64    inference(resolution,[],[f1739,f50])).
% 2.09/0.64  fof(f1739,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | ~spl7_82),
% 2.09/0.64    inference(avatar_component_clause,[],[f1738])).
% 2.09/0.64  fof(f1738,plain,(
% 2.09/0.64    spl7_82 <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 2.09/0.64  fof(f1740,plain,(
% 2.09/0.64    spl7_82 | ~spl7_64 | ~spl7_2 | ~spl7_3 | ~spl7_77),
% 2.09/0.64    inference(avatar_split_clause,[],[f1673,f1650,f82,f77,f1394,f1738])).
% 2.09/0.64  fof(f1394,plain,(
% 2.09/0.64    spl7_64 <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 2.09/0.64  fof(f1650,plain,(
% 2.09/0.64    spl7_77 <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 2.09/0.64  fof(f1673,plain,(
% 2.09/0.64    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | (~spl7_2 | ~spl7_3 | ~spl7_77)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1672,f78])).
% 2.09/0.64  fof(f1672,plain,(
% 2.09/0.64    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | (~spl7_3 | ~spl7_77)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1665,f83])).
% 2.09/0.64  fof(f1665,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | ~spl7_77),
% 2.09/0.64    inference(resolution,[],[f1651,f66])).
% 2.09/0.64  fof(f66,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f32])).
% 2.09/0.64  fof(f32,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f11])).
% 2.09/0.64  fof(f11,axiom,(
% 2.09/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 2.09/0.64  fof(f1651,plain,(
% 2.09/0.64    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | ~spl7_77),
% 2.09/0.64    inference(avatar_component_clause,[],[f1650])).
% 2.09/0.64  fof(f1652,plain,(
% 2.09/0.64    spl7_77 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_48),
% 2.09/0.64    inference(avatar_split_clause,[],[f1639,f798,f204,f82,f77,f73,f1650])).
% 2.09/0.64  fof(f73,plain,(
% 2.09/0.64    spl7_1 <=> v4_orders_2(sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.09/0.64  fof(f204,plain,(
% 2.09/0.64    spl7_17 <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.09/0.64  fof(f798,plain,(
% 2.09/0.64    spl7_48 <=> r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.09/0.64  fof(f1639,plain,(
% 2.09/0.64    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_17 | ~spl7_48)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1636,f83])).
% 2.09/0.64  fof(f1636,plain,(
% 2.09/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_17 | ~spl7_48)),
% 2.09/0.64    inference(resolution,[],[f238,f799])).
% 2.09/0.64  fof(f799,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~spl7_48),
% 2.09/0.64    inference(avatar_component_clause,[],[f798])).
% 2.09/0.64  fof(f238,plain,(
% 2.09/0.64    ( ! [X0] : (~r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_17)),
% 2.09/0.64    inference(subsumption_resolution,[],[f237,f74])).
% 2.09/0.64  fof(f74,plain,(
% 2.09/0.64    v4_orders_2(sK0) | ~spl7_1),
% 2.09/0.64    inference(avatar_component_clause,[],[f73])).
% 2.09/0.64  fof(f237,plain,(
% 2.09/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0)) ) | (~spl7_2 | ~spl7_17)),
% 2.09/0.64    inference(subsumption_resolution,[],[f236,f80])).
% 2.09/0.64  fof(f80,plain,(
% 2.09/0.64    ( ! [X0] : (m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))) ) | ~spl7_2),
% 2.09/0.64    inference(resolution,[],[f78,f51])).
% 2.09/0.64  fof(f51,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f23])).
% 2.09/0.64  fof(f23,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f9])).
% 2.09/0.64  fof(f9,axiom,(
% 2.09/0.64    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).
% 2.09/0.64  fof(f236,plain,(
% 2.09/0.64    ( ! [X0] : (~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0)) ) | (~spl7_2 | ~spl7_17)),
% 2.09/0.64    inference(subsumption_resolution,[],[f230,f78])).
% 2.09/0.64  fof(f230,plain,(
% 2.09/0.64    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),X0)) ) | ~spl7_17),
% 2.09/0.64    inference(resolution,[],[f205,f62])).
% 2.09/0.64  fof(f62,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_lattice3(X0,X1,X3)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f31])).
% 2.09/0.64  fof(f31,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : (! [X3] : (r1_lattice3(X0,X1,X3) | ~r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 2.09/0.64    inference(flattening,[],[f30])).
% 2.09/0.64  fof(f30,plain,(
% 2.09/0.64    ! [X0] : (! [X1,X2] : (! [X3] : ((r1_lattice3(X0,X1,X3) | (~r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f10])).
% 2.09/0.64  fof(f10,axiom,(
% 2.09/0.64    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X2)) => r1_lattice3(X0,X1,X3)))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_0)).
% 2.09/0.64  fof(f205,plain,(
% 2.09/0.64    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~spl7_17),
% 2.09/0.64    inference(avatar_component_clause,[],[f204])).
% 2.09/0.64  fof(f1414,plain,(
% 2.09/0.64    ~spl7_2 | ~spl7_3 | spl7_7 | spl7_64),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f1413])).
% 2.09/0.64  fof(f1413,plain,(
% 2.09/0.64    $false | (~spl7_2 | ~spl7_3 | spl7_7 | spl7_64)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1412,f123])).
% 2.09/0.64  fof(f1412,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | spl7_64)),
% 2.09/0.64    inference(resolution,[],[f1395,f89])).
% 2.09/0.64  fof(f89,plain,(
% 2.09/0.64    ( ! [X2] : (m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,X2,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(subsumption_resolution,[],[f86,f78])).
% 2.09/0.64  fof(f86,plain,(
% 2.09/0.64    ( ! [X2] : (~l1_orders_2(sK0) | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,X2,sK3)) ) | ~spl7_3),
% 2.09/0.64    inference(resolution,[],[f83,f48])).
% 2.09/0.64  fof(f48,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f22])).
% 2.09/0.64  fof(f1395,plain,(
% 2.09/0.64    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | spl7_64),
% 2.09/0.64    inference(avatar_component_clause,[],[f1394])).
% 2.09/0.64  fof(f800,plain,(
% 2.09/0.64    spl7_48 | ~spl7_2 | ~spl7_3 | ~spl7_8 | ~spl7_18),
% 2.09/0.64    inference(avatar_split_clause,[],[f796,f242,f109,f82,f77,f798])).
% 2.09/0.64  fof(f242,plain,(
% 2.09/0.64    spl7_18 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.09/0.64  fof(f796,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | (~spl7_2 | ~spl7_3 | ~spl7_8 | ~spl7_18)),
% 2.09/0.64    inference(subsumption_resolution,[],[f795,f83])).
% 2.09/0.64  fof(f795,plain,(
% 2.09/0.64    r1_orders_2(sK0,sK3,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_2 | ~spl7_8 | ~spl7_18)),
% 2.09/0.64    inference(resolution,[],[f635,f110])).
% 2.09/0.64  fof(f110,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | ~spl7_8),
% 2.09/0.64    inference(avatar_component_clause,[],[f109])).
% 2.09/0.64  fof(f635,plain,(
% 2.09/0.64    ( ! [X0] : (~r1_lattice3(sK0,sK2,X0) | r1_orders_2(sK0,X0,k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_2 | ~spl7_18)),
% 2.09/0.64    inference(resolution,[],[f243,f146])).
% 2.09/0.64  fof(f146,plain,(
% 2.09/0.64    ( ! [X6,X8,X7] : (~r2_hidden(k2_yellow_0(sK0,X7),X8) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7)) | ~r1_lattice3(sK0,X8,X6)) ) | ~spl7_2),
% 2.09/0.64    inference(subsumption_resolution,[],[f141,f78])).
% 2.09/0.64  fof(f141,plain,(
% 2.09/0.64    ( ! [X6,X8,X7] : (~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_hidden(k2_yellow_0(sK0,X7),X8) | r1_orders_2(sK0,X6,k2_yellow_0(sK0,X7)) | ~r1_lattice3(sK0,X8,X6)) ) | ~spl7_2),
% 2.09/0.64    inference(resolution,[],[f80,f47])).
% 2.09/0.64  fof(f47,plain,(
% 2.09/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f22])).
% 2.09/0.64  fof(f243,plain,(
% 2.09/0.64    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | ~spl7_18),
% 2.09/0.64    inference(avatar_component_clause,[],[f242])).
% 2.09/0.64  fof(f630,plain,(
% 2.09/0.64    ~spl7_7 | ~spl7_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f112,f109,f106])).
% 2.09/0.64  fof(f112,plain,(
% 2.09/0.64    ~r1_lattice3(sK0,sK1,sK3) | ~spl7_8),
% 2.09/0.64    inference(subsumption_resolution,[],[f39,f110])).
% 2.09/0.64  fof(f39,plain,(
% 2.09/0.64    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f20,plain,(
% 2.09/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 2.09/0.64    inference(flattening,[],[f19])).
% 2.09/0.64  fof(f19,plain,(
% 2.09/0.64    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f18])).
% 2.09/0.64  fof(f18,plain,(
% 2.09/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 2.09/0.64    inference(pure_predicate_removal,[],[f17])).
% 2.09/0.64  fof(f17,plain,(
% 2.09/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 2.09/0.64    inference(pure_predicate_removal,[],[f15])).
% 2.09/0.64  fof(f15,plain,(
% 2.09/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 2.09/0.64    inference(rectify,[],[f14])).
% 2.09/0.64  fof(f14,negated_conjecture,(
% 2.09/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 2.09/0.64    inference(negated_conjecture,[],[f13])).
% 2.09/0.64  fof(f13,conjecture,(
% 2.09/0.64    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).
% 2.09/0.64  fof(f548,plain,(
% 2.09/0.64    spl7_34 | ~spl7_2 | ~spl7_32),
% 2.09/0.64    inference(avatar_split_clause,[],[f525,f464,f77,f546])).
% 2.09/0.64  fof(f525,plain,(
% 2.09/0.64    m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_2 | ~spl7_32)),
% 2.09/0.64    inference(superposition,[],[f80,f465])).
% 2.09/0.64  fof(f466,plain,(
% 2.09/0.64    spl7_32 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f444,f109,f82,f77,f464])).
% 2.09/0.64  fof(f444,plain,(
% 2.09/0.64    sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.09/0.64    inference(subsumption_resolution,[],[f439,f260])).
% 2.09/0.64  fof(f439,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f438])).
% 2.09/0.64  fof(f438,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r1_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f160,f90])).
% 2.09/0.64  fof(f90,plain,(
% 2.09/0.64    ( ! [X3] : (r2_hidden(sK5(sK0,X3,sK3),X3) | r1_lattice3(sK0,X3,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(subsumption_resolution,[],[f87,f78])).
% 2.09/0.64  fof(f87,plain,(
% 2.09/0.64    ( ! [X3] : (~l1_orders_2(sK0) | r2_hidden(sK5(sK0,X3,sK3),X3) | r1_lattice3(sK0,X3,sK3)) ) | ~spl7_3),
% 2.09/0.64    inference(resolution,[],[f83,f49])).
% 2.09/0.64  fof(f49,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f22])).
% 2.09/0.64  fof(f160,plain,(
% 2.09/0.64    ( ! [X0] : (~r2_hidden(sK5(sK0,X0,sK3),sK2) | r1_lattice3(sK0,X0,sK3) | sK5(sK0,X0,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,X0,sK3)))) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f89,f37])).
% 2.09/0.64  fof(f37,plain,(
% 2.09/0.64    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | k2_yellow_0(sK0,sK4(X4)) = X4) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f415,plain,(
% 2.09/0.64    spl7_30 | ~spl7_28),
% 2.09/0.64    inference(avatar_split_clause,[],[f400,f362,f413])).
% 2.09/0.64  fof(f362,plain,(
% 2.09/0.64    spl7_28 <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.09/0.64  fof(f400,plain,(
% 2.09/0.64    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_28),
% 2.09/0.64    inference(resolution,[],[f363,f61])).
% 2.09/0.64  fof(f61,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f29])).
% 2.09/0.64  fof(f29,plain,(
% 2.09/0.64    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.09/0.64    inference(ennf_transformation,[],[f16])).
% 2.09/0.64  fof(f16,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.09/0.64    inference(unused_predicate_definition_removal,[],[f4])).
% 2.09/0.64  fof(f4,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.09/0.64  fof(f363,plain,(
% 2.09/0.64    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_28),
% 2.09/0.64    inference(avatar_component_clause,[],[f362])).
% 2.09/0.64  fof(f364,plain,(
% 2.09/0.64    spl7_28 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f351,f109,f82,f77,f362])).
% 2.09/0.64  fof(f351,plain,(
% 2.09/0.64    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.09/0.64    inference(subsumption_resolution,[],[f346,f260])).
% 2.09/0.64  fof(f346,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f345])).
% 2.09/0.64  fof(f345,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f161,f90])).
% 2.09/0.64  fof(f161,plain,(
% 2.09/0.64    ( ! [X1] : (~r2_hidden(sK5(sK0,X1,sK3),sK2) | r1_lattice3(sK0,X1,sK3) | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1))) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f89,f35])).
% 2.09/0.64  fof(f35,plain,(
% 2.09/0.64    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f329,plain,(
% 2.09/0.64    spl7_26 | ~spl7_2 | ~spl7_3 | spl7_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f325,f109,f82,f77,f327])).
% 2.09/0.64  fof(f325,plain,(
% 2.09/0.64    r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3 | spl7_8)),
% 2.09/0.64    inference(subsumption_resolution,[],[f324,f260])).
% 2.09/0.64  fof(f324,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f323])).
% 2.09/0.64  fof(f323,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r1_lattice3(sK0,sK2,sK3) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f162,f90])).
% 2.09/0.64  fof(f162,plain,(
% 2.09/0.64    ( ! [X2] : (~r2_hidden(sK5(sK0,X2,sK3),sK2) | r1_lattice3(sK0,X2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,X2,sK3)))) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f89,f36])).
% 2.09/0.64  fof(f36,plain,(
% 2.09/0.64    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | r2_yellow_0(sK0,sK4(X4))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f244,plain,(
% 2.09/0.64    spl7_18 | spl7_16 | ~spl7_2 | ~spl7_3 | spl7_7),
% 2.09/0.64    inference(avatar_split_clause,[],[f185,f106,f82,f77,f199,f242])).
% 2.09/0.64  fof(f199,plain,(
% 2.09/0.64    spl7_16 <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.09/0.64  fof(f185,plain,(
% 2.09/0.64    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.09/0.64    inference(subsumption_resolution,[],[f184,f60])).
% 2.09/0.64  fof(f60,plain,(
% 2.09/0.64    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f6])).
% 2.09/0.64  fof(f6,axiom,(
% 2.09/0.64    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 2.09/0.64  fof(f184,plain,(
% 2.09/0.64    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.09/0.64    inference(subsumption_resolution,[],[f182,f123])).
% 2.09/0.64  fof(f182,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f158,f41])).
% 2.09/0.64  fof(f41,plain,(
% 2.09/0.64    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~v1_finset_1(X3) | k1_xboole_0 = X3 | r2_hidden(k2_yellow_0(sK0,X3),sK2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f158,plain,(
% 2.09/0.64    ( ! [X0] : (m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0)) | r1_lattice3(sK0,X0,sK3)) ) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f90,f58])).
% 2.09/0.64  fof(f58,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f28])).
% 2.09/0.64  fof(f28,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.09/0.64    inference(ennf_transformation,[],[f3])).
% 2.09/0.64  fof(f3,axiom,(
% 2.09/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 2.09/0.64  fof(f216,plain,(
% 2.09/0.64    ~spl7_16),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f215])).
% 2.09/0.64  fof(f215,plain,(
% 2.09/0.64    $false | ~spl7_16),
% 2.09/0.64    inference(subsumption_resolution,[],[f209,f59])).
% 2.09/0.64  fof(f59,plain,(
% 2.09/0.64    v1_xboole_0(k1_xboole_0)),
% 2.09/0.64    inference(cnf_transformation,[],[f1])).
% 2.09/0.64  fof(f1,axiom,(
% 2.09/0.64    v1_xboole_0(k1_xboole_0)),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.09/0.64  fof(f209,plain,(
% 2.09/0.64    ~v1_xboole_0(k1_xboole_0) | ~spl7_16),
% 2.09/0.64    inference(superposition,[],[f67,f200])).
% 2.09/0.64  fof(f200,plain,(
% 2.09/0.64    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | ~spl7_16),
% 2.09/0.64    inference(avatar_component_clause,[],[f199])).
% 2.09/0.64  fof(f67,plain,(
% 2.09/0.64    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f2])).
% 2.09/0.64  fof(f2,axiom,(
% 2.09/0.64    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.09/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.09/0.64  fof(f206,plain,(
% 2.09/0.64    spl7_17 | ~spl7_2 | ~spl7_15),
% 2.09/0.64    inference(avatar_split_clause,[],[f202,f196,f77,f204])).
% 2.09/0.64  fof(f196,plain,(
% 2.09/0.64    spl7_15 <=> r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.09/0.64  fof(f202,plain,(
% 2.09/0.64    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))) | (~spl7_2 | ~spl7_15)),
% 2.09/0.64    inference(resolution,[],[f197,f145])).
% 2.09/0.64  fof(f145,plain,(
% 2.09/0.64    ( ! [X2] : (~r2_yellow_0(sK0,X2) | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))) ) | ~spl7_2),
% 2.09/0.64    inference(subsumption_resolution,[],[f137,f78])).
% 2.09/0.64  fof(f137,plain,(
% 2.09/0.64    ( ! [X2] : (~l1_orders_2(sK0) | ~r2_yellow_0(sK0,X2) | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))) ) | ~spl7_2),
% 2.09/0.64    inference(resolution,[],[f80,f70])).
% 2.09/0.64  fof(f70,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))) )),
% 2.09/0.64    inference(equality_resolution,[],[f56])).
% 2.09/0.64  fof(f56,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2) )),
% 2.09/0.64    inference(cnf_transformation,[],[f25])).
% 2.09/0.64  fof(f197,plain,(
% 2.09/0.64    r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~spl7_15),
% 2.09/0.64    inference(avatar_component_clause,[],[f196])).
% 2.09/0.64  fof(f201,plain,(
% 2.09/0.64    spl7_15 | spl7_16 | ~spl7_2 | ~spl7_3 | spl7_7),
% 2.09/0.64    inference(avatar_split_clause,[],[f187,f106,f82,f77,f199,f196])).
% 2.09/0.64  fof(f187,plain,(
% 2.09/0.64    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.09/0.64    inference(subsumption_resolution,[],[f186,f60])).
% 2.09/0.64  fof(f186,plain,(
% 2.09/0.64    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3 | spl7_7)),
% 2.09/0.64    inference(subsumption_resolution,[],[f183,f123])).
% 2.09/0.64  fof(f183,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_2 | ~spl7_3)),
% 2.09/0.64    inference(resolution,[],[f158,f42])).
% 2.09/0.64  fof(f42,plain,(
% 2.09/0.64    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(sK1)) | ~v1_finset_1(X6) | k1_xboole_0 = X6 | r2_yellow_0(sK0,X6)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f111,plain,(
% 2.09/0.64    spl7_7 | spl7_8),
% 2.09/0.64    inference(avatar_split_clause,[],[f38,f109,f106])).
% 2.09/0.64  fof(f38,plain,(
% 2.09/0.64    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f84,plain,(
% 2.09/0.64    spl7_3),
% 2.09/0.64    inference(avatar_split_clause,[],[f40,f82])).
% 2.09/0.64  fof(f40,plain,(
% 2.09/0.64    m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f79,plain,(
% 2.09/0.64    spl7_2),
% 2.09/0.64    inference(avatar_split_clause,[],[f46,f77])).
% 2.09/0.64  fof(f46,plain,(
% 2.09/0.64    l1_orders_2(sK0)),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  fof(f75,plain,(
% 2.09/0.64    spl7_1),
% 2.09/0.64    inference(avatar_split_clause,[],[f45,f73])).
% 2.09/0.64  fof(f45,plain,(
% 2.09/0.64    v4_orders_2(sK0)),
% 2.09/0.64    inference(cnf_transformation,[],[f20])).
% 2.09/0.64  % SZS output end Proof for theBenchmark
% 2.09/0.64  % (24608)------------------------------
% 2.09/0.64  % (24608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.64  % (24608)Termination reason: Refutation
% 2.09/0.64  
% 2.09/0.64  % (24608)Memory used [KB]: 7675
% 2.09/0.64  % (24608)Time elapsed: 0.209 s
% 2.09/0.64  % (24608)------------------------------
% 2.09/0.64  % (24608)------------------------------
% 2.09/0.65  % (24607)Success in time 0.29 s
%------------------------------------------------------------------------------
