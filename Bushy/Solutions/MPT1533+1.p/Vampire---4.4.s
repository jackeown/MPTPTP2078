%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t11_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 273 expanded)
%              Number of leaves         :   33 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  384 (1130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f86,f93,f100,f107,f114,f121,f138,f152,f164,f172,f181,f189,f204,f211,f224,f231,f239])).

fof(f239,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_32
    | spl7_35 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f235,f232])).

fof(f232,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK2)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f78,f92,f106,f137,f223,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',d9_lattice3)).

fof(f223,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_32
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f137,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_16
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f106,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_10
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f92,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f235,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK2)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f71,f78,f113,f92,f99,f223,f230,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',t26_orders_2)).

fof(f230,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl7_35
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f99,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_8
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f113,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_12
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f71,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_0
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f231,plain,
    ( ~ spl7_35
    | ~ spl7_2
    | ~ spl7_8
    | spl7_15 ),
    inference(avatar_split_clause,[],[f182,f119,f98,f77,f229])).

fof(f119,plain,
    ( spl7_15
  <=> ~ r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f182,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f78,f120,f99,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f224,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_8
    | spl7_15 ),
    inference(avatar_split_clause,[],[f157,f119,f98,f77,f222])).

fof(f157,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f78,f120,f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f211,plain,
    ( ~ spl7_31
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f141,f136,f209])).

fof(f209,plain,
    ( spl7_31
  <=> ~ r2_hidden(sK1,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f141,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK3))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',antisymmetry_r2_hidden)).

fof(f204,plain,
    ( spl7_28
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f139,f136,f202])).

fof(f202,plain,
    ( spl7_28
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f139,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f137,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',t1_subset)).

fof(f189,plain,
    ( spl7_26
    | spl7_19 ),
    inference(avatar_split_clause,[],[f155,f150,f187])).

fof(f187,plain,
    ( spl7_26
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f150,plain,
    ( spl7_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f155,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f59,f151,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',t2_subset)).

fof(f151,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',existence_m1_subset_1)).

fof(f181,plain,
    ( ~ spl7_25
    | spl7_19 ),
    inference(avatar_split_clause,[],[f154,f150,f179])).

fof(f179,plain,
    ( spl7_25
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f59,f151,f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f62,f60])).

fof(f172,plain,
    ( ~ spl7_23
    | spl7_21 ),
    inference(avatar_split_clause,[],[f165,f162,f170])).

fof(f170,plain,
    ( spl7_23
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f162,plain,
    ( spl7_21
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f165,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f163,f61])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( ~ spl7_21
    | spl7_19 ),
    inference(avatar_split_clause,[],[f153,f150,f162])).

fof(f153,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f151,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f123,f62])).

fof(f152,plain,
    ( ~ spl7_19
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f142,f136,f150])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f137,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',t7_boole)).

fof(f138,plain,
    ( spl7_16
    | ~ spl7_2
    | ~ spl7_8
    | spl7_15 ),
    inference(avatar_split_clause,[],[f130,f119,f98,f77,f136])).

fof(f130,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f78,f120,f99,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r2_lattice3(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r2_lattice3(X0,X1,X3)
                & r1_orders_2(X0,X2,X3)
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r2_lattice3(sK0,X1,X3)
              & r1_orders_2(sK0,X2,X3)
              & r2_lattice3(sK0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_lattice3(X0,sK1,X3)
            & r1_orders_2(X0,sK2,X3)
            & r2_lattice3(X0,sK1,sK2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_lattice3(X0,X1,X3)
          & r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_lattice3(X0,X1,sK3)
        & r1_orders_2(X0,X2,sK3)
        & r2_lattice3(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X2) )
                 => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X2) )
               => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',t11_yellow_0)).

fof(f114,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f51,f112])).

fof(f51,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f65,f84])).

fof(f84,plain,
    ( spl7_4
  <=> l1_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f65,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    l1_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f10,f44])).

fof(f44,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK6) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t11_yellow_0.p',existence_l1_orders_2)).

fof(f79,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f47,f77])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f46,f70])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
