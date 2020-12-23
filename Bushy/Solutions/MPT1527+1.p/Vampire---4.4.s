%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t5_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 469 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          :  691 (1980 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5013,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f91,f95,f120,f137,f145,f1788,f1791,f1800,f1804,f1828,f4875,f4884,f5004,f5012])).

fof(f5012,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | spl11_15
    | ~ spl11_52 ),
    inference(avatar_contradiction_clause,[],[f5011])).

fof(f5011,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_15
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f5010,f1799])).

fof(f1799,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1798,plain,
    ( spl11_15
  <=> ~ r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f5010,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f5009,f85])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl11_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f5009,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_6
    | ~ spl11_52 ),
    inference(subsumption_resolution,[],[f5008,f94])).

fof(f94,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl11_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f5008,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_52 ),
    inference(resolution,[],[f5003,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d8_lattice3)).

fof(f5003,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f5002])).

fof(f5002,plain,
    ( spl11_52
  <=> r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f5004,plain,
    ( spl11_52
    | ~ spl11_2
    | ~ spl11_6
    | spl11_11
    | spl11_15
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f5000,f1802,f1798,f139,f93,f84,f5002])).

fof(f139,plain,
    ( spl11_11
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f1802,plain,
    ( spl11_20
  <=> r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f5000,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f4999,f94])).

fof(f4999,plain,
    ( r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f4995,f1799])).

fof(f4995,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_20 ),
    inference(resolution,[],[f393,f1803])).

fof(f1803,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f393,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),X4)
        | r1_lattice3(sK0,X5,sK2)
        | r1_orders_2(sK0,X4,sK4(sK0,X5,sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattice3(sK0,X5,sK2)
        | r1_orders_2(sK0,X4,sK4(sK0,X5,sK2))
        | ~ r1_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),X4)
        | r1_lattice3(sK0,X5,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f185,f268])).

fof(f268,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,X2,sK2),k3_xboole_0(X2,u1_struct_0(sK0)))
        | r1_lattice3(sK0,X2,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f256,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d4_xboole_0)).

fof(f256,plain,
    ( ! [X1] :
        ( sP6(sK4(sK0,X1,sK2),u1_struct_0(sK0),X1)
        | r1_lattice3(sK0,X1,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK2)
        | sP6(sK4(sK0,X1,sK2),u1_struct_0(sK0),X1)
        | r1_lattice3(sK0,X1,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f159,f188])).

fof(f188,plain,
    ( ! [X14] :
        ( r2_hidden(sK4(sK0,X14,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X14,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f181,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f181,plain,
    ( ! [X14] :
        ( r1_lattice3(sK0,X14,sK2)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,X14,sK2),u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',t2_subset)).

fof(f107,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,X6,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X6,sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f100,f85])).

fof(f100,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK4(sK0,X6,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X6,sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f94,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f159,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK4(sK0,X5,sK2),X6)
        | r1_lattice3(sK0,X5,sK2)
        | sP6(sK4(sK0,X5,sK2),X6,X5) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f108,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,plain,
    ( ! [X7] :
        ( r2_hidden(sK4(sK0,X7,sK2),X7)
        | r1_lattice3(sK0,X7,sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f101,f85])).

fof(f101,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,X7,sK2),X7)
        | r1_lattice3(sK0,X7,sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f185,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(sK4(sK0,X7,sK2),X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_lattice3(sK0,X7,sK2)
        | r1_orders_2(sK0,X8,sK4(sK0,X7,sK2))
        | ~ r1_lattice3(sK0,X9,X8) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f178,f85])).

fof(f178,plain,
    ( ! [X8,X7,X9] :
        ( r1_lattice3(sK0,X7,sK2)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK4(sK0,X7,sK2),X9)
        | r1_orders_2(sK0,X8,sK4(sK0,X7,sK2))
        | ~ r1_lattice3(sK0,X9,X8) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4884,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | spl11_19
    | ~ spl11_48 ),
    inference(avatar_contradiction_clause,[],[f4883])).

fof(f4883,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_19
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f4882,f1844])).

fof(f1844,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f1843,plain,
    ( spl11_19
  <=> ~ r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f4882,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f4881,f85])).

fof(f4881,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_6
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f4880,f94])).

fof(f4880,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_48 ),
    inference(resolution,[],[f4874,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
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
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',d9_lattice3)).

fof(f4874,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f4873])).

fof(f4873,plain,
    ( spl11_48
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f4875,plain,
    ( spl11_48
    | ~ spl11_2
    | ~ spl11_6
    | spl11_11
    | ~ spl11_16
    | spl11_19 ),
    inference(avatar_split_clause,[],[f4871,f1843,f132,f139,f93,f84,f4873])).

fof(f132,plain,
    ( spl11_16
  <=> r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f4871,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f4870,f94])).

fof(f4870,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_16
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f4866,f1844])).

fof(f4866,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK7(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11
    | ~ spl11_16 ),
    inference(resolution,[],[f359,f133])).

fof(f133,plain,
    ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f359,plain,
    ( ! [X4,X5] :
        ( ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),X4)
        | r2_lattice3(sK0,X5,sK2)
        | r1_orders_2(sK0,sK7(sK0,X5,sK2),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_lattice3(sK0,X5,sK2)
        | r1_orders_2(sK0,sK7(sK0,X5,sK2),X4)
        | ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),X4)
        | r2_lattice3(sK0,X5,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f167,f260])).

fof(f260,plain,
    ( ! [X2] :
        ( r2_hidden(sK7(sK0,X2,sK2),k3_xboole_0(X2,u1_struct_0(sK0)))
        | r2_lattice3(sK0,X2,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f248,f78])).

fof(f248,plain,
    ( ! [X1] :
        ( sP6(sK7(sK0,X1,sK2),u1_struct_0(sK0),X1)
        | r2_lattice3(sK0,X1,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ! [X1] :
        ( r2_lattice3(sK0,X1,sK2)
        | sP6(sK7(sK0,X1,sK2),u1_struct_0(sK0),X1)
        | r2_lattice3(sK0,X1,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(resolution,[],[f154,f173])).

fof(f173,plain,
    ( ! [X14] :
        ( r2_hidden(sK7(sK0,X14,sK2),u1_struct_0(sK0))
        | r2_lattice3(sK0,X14,sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f166,f140])).

fof(f166,plain,
    ( ! [X14] :
        ( r2_lattice3(sK0,X14,sK2)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK7(sK0,X14,sK2),u1_struct_0(sK0)) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f104,f67])).

fof(f104,plain,
    ( ! [X2] :
        ( m1_subset_1(sK7(sK0,X2,sK2),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f97,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK7(sK0,X2,sK2),u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f154,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK7(sK0,X5,sK2),X6)
        | r2_lattice3(sK0,X5,sK2)
        | sP6(sK7(sK0,X5,sK2),X6,X5) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f105,f54])).

fof(f105,plain,
    ( ! [X3] :
        ( r2_hidden(sK7(sK0,X3,sK2),X3)
        | r2_lattice3(sK0,X3,sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f98,f85])).

fof(f98,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK7(sK0,X3,sK2),X3)
        | r2_lattice3(sK0,X3,sK2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK7(sK0,X0,sK2),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK2)
        | r1_orders_2(sK0,sK7(sK0,X0,sK2),X1)
        | ~ r2_lattice3(sK0,X2,X1) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f160,f85])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK7(sK0,X0,sK2),X2)
        | r1_orders_2(sK0,sK7(sK0,X0,sK2),X1)
        | ~ r2_lattice3(sK0,X2,X1) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1828,plain,
    ( spl11_12
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f1820,f1802,f135,f93,f84,f126])).

fof(f126,plain,
    ( spl11_12
  <=> sP3(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f135,plain,
    ( spl11_18
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f1820,plain,
    ( sP3(sK2,sK1,sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f1819,f1803])).

fof(f1819,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | sP3(sK2,sK1,sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1818,f136])).

fof(f136,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1818,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | sP3(sK2,sK1,sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f46,f1648])).

fof(f1648,plain,
    ( ! [X0] : r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1647,f85])).

fof(f1647,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1646,f94])).

fof(f1646,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f1642])).

fof(f1642,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(resolution,[],[f1641,f66])).

fof(f1641,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK7(sK0,k3_xboole_0(sK1,X0),sK2),sK2)
        | r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1640,f94])).

fof(f1640,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK7(sK0,k3_xboole_0(sK1,X0),sK2),sK2)
        | r2_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(resolution,[],[f411,f136])).

fof(f411,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_lattice3(sK0,X3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK7(sK0,k3_xboole_0(X3,X4),sK2),X5)
        | r2_lattice3(sK0,k3_xboole_0(X3,X4),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,
    ( ! [X4,X5,X3] :
        ( r2_lattice3(sK0,k3_xboole_0(X3,X4),sK2)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_lattice3(sK0,k3_xboole_0(X3,X4),sK2)
        | r1_orders_2(sK0,sK7(sK0,k3_xboole_0(X3,X4),sK2),X5)
        | ~ r2_lattice3(sK0,X3,X5) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f228,f167])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK0,k3_xboole_0(X0,X1),sK2),X0)
        | r2_lattice3(sK0,k3_xboole_0(X0,X1),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f150,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( sP6(sK7(sK0,k3_xboole_0(X0,X1),sK2),X1,X0)
        | r2_lattice3(sK0,k3_xboole_0(X0,X1),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f105,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,
    ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ( ~ r1_lattice3(X0,X1,X2)
              & r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r1_lattice3(X0,X1,X2) )
            | ( ~ r2_lattice3(X0,X1,X2)
              & r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r2_lattice3(X0,X1,X2) ) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ( ~ r1_lattice3(X0,X1,X2)
              & r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r1_lattice3(X0,X1,X2) )
            | ( ~ r2_lattice3(X0,X1,X2)
              & r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r2_lattice3(X0,X1,X2) ) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
               => r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,X1,X2)
               => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
              & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
               => r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,X1,X2)
               => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',t5_yellow_0)).

fof(f1804,plain,
    ( spl11_20
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f1792,f126,f1802])).

fof(f1792,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f127,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f127,plain,
    ( sP3(sK2,sK1,sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1800,plain,
    ( ~ spl11_15
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f1793,f126,f1798])).

fof(f1793,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f127,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1791,plain,
    ( spl11_12
    | spl11_14
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f1790,f135,f93,f84,f129,f126])).

fof(f129,plain,
    ( spl11_14
  <=> r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f1790,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | sP3(sK2,sK1,sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f1789,f136])).

fof(f1789,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | sP3(sK2,sK1,sK0)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f45,f1648])).

fof(f45,plain,
    ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1788,plain,
    ( ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f1787])).

fof(f1787,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f144,f1786])).

fof(f1786,plain,
    ( ! [X0] : r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1785,f85])).

fof(f1785,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1784,f94])).

fof(f1784,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(duplicate_literal_removal,[],[f1780])).

fof(f1780,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(resolution,[],[f1779,f53])).

fof(f1779,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,k3_xboole_0(sK1,X0),sK2))
        | r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f1778,f94])).

fof(f1778,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK4(sK0,k3_xboole_0(sK1,X0),sK2))
        | r1_lattice3(sK0,k3_xboole_0(sK1,X0),sK2) )
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_14 ),
    inference(resolution,[],[f442,f130])).

fof(f130,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f442,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_xboole_0(X0,X1),sK2))
        | r1_lattice3(sK0,k3_xboole_0(X0,X1),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,k3_xboole_0(X0,X1),sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,k3_xboole_0(X0,X1),sK2)
        | r1_orders_2(sK0,X2,sK4(sK0,k3_xboole_0(X0,X1),sK2))
        | ~ r1_lattice3(sK0,X0,X2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f235,f185])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,k3_xboole_0(X0,X1),sK2),X0)
        | r1_lattice3(sK0,k3_xboole_0(X0,X1),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f155,f55])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( sP6(sK4(sK0,k3_xboole_0(X0,X1),sK2),X1,X0)
        | r1_lattice3(sK0,k3_xboole_0(X0,X1),sK2) )
    | ~ spl11_2
    | ~ spl11_6 ),
    inference(resolution,[],[f108,f77])).

fof(f144,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_21
  <=> ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f145,plain,
    ( spl11_12
    | ~ spl11_21
    | spl11_16
    | spl11_18 ),
    inference(avatar_split_clause,[],[f44,f135,f132,f143,f126])).

fof(f44,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( spl11_12
    | spl11_14
    | spl11_16
    | spl11_18 ),
    inference(avatar_split_clause,[],[f43,f135,f132,f129,f126])).

fof(f43,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f120,plain,
    ( spl11_1
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f118,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f118,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f116,f90])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl11_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f116,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_10 ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',fc2_struct_0)).

fof(f114,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl11_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f95,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,
    ( spl11_4
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f87,f84,f89])).

fof(f87,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f85,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t5_yellow_0.p',dt_l1_orders_2)).

fof(f86,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f49,f84])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
