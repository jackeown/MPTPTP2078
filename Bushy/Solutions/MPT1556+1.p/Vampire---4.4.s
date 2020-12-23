%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t34_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 244 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  390 ( 815 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f81,f85,f90,f94,f155,f196,f257,f530,f540])).

fof(f540,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | spl7_11
    | ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f538,f93])).

fof(f93,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_11
  <=> ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f538,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f537,f80])).

fof(f80,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_4
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f537,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f533,f73])).

fof(f73,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl7_0 ),
    inference(resolution,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',dt_k1_yellow_0)).

fof(f71,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f533,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_46 ),
    inference(resolution,[],[f529,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f96,f71])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl7_0 ),
    inference(resolution,[],[f73,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',d9_yellow_0)).

fof(f529,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl7_46
  <=> r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f530,plain,
    ( spl7_46
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | spl7_29 ),
    inference(avatar_split_clause,[],[f513,f191,f153,f88,f70,f528])).

fof(f88,plain,
    ( spl7_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f153,plain,
    ( spl7_22
  <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f191,plain,
    ( spl7_29
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f513,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f512,f71])).

fof(f512,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f511,f73])).

fof(f511,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f510])).

fof(f510,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(resolution,[],[f508,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',d9_lattice3)).

fof(f508,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,k1_yellow_0(sK0,X0)),k1_yellow_0(sK0,sK2))
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f507,f73])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,k1_yellow_0(sK0,X0)),k1_yellow_0(sK0,sK2))
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_22
    | ~ spl7_29 ),
    inference(resolution,[],[f246,f154])).

fof(f154,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,k1_yellow_0(sK0,X0)),X1)
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0))
        | r1_orders_2(sK0,sK3(sK0,sK1,k1_yellow_0(sK0,X0)),X1)
        | ~ r2_lattice3(sK0,sK2,X1) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(resolution,[],[f239,f142])).

fof(f142,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK3(sK0,X0,k1_yellow_0(sK0,X1)),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,X1))
        | r1_orders_2(sK0,sK3(sK0,X0,k1_yellow_0(sK0,X1)),X2)
        | ~ r2_lattice3(sK0,X3,X2) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f138,f71])).

fof(f138,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_lattice3(sK0,X0,k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK3(sK0,X0,k1_yellow_0(sK0,X1)),X3)
        | r1_orders_2(sK0,sK3(sK0,X0,k1_yellow_0(sK0,X1)),X2)
        | ~ r2_lattice3(sK0,X3,X2) )
    | ~ spl7_0 ),
    inference(resolution,[],[f105,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,
    ( ! [X6,X7] :
        ( m1_subset_1(sK3(sK0,X6,k1_yellow_0(sK0,X7)),u1_struct_0(sK0))
        | r2_lattice3(sK0,X6,k1_yellow_0(sK0,X7)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f99,f71])).

fof(f99,plain,
    ( ! [X6,X7] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK3(sK0,X6,k1_yellow_0(sK0,X7)),u1_struct_0(sK0))
        | r2_lattice3(sK0,X6,k1_yellow_0(sK0,X7)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f239,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,k1_yellow_0(sK0,X0)),sK2)
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_8
    | ~ spl7_29 ),
    inference(subsumption_resolution,[],[f238,f192])).

fof(f192,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f191])).

fof(f238,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0))
        | v1_xboole_0(sK2)
        | r2_hidden(sK3(sK0,sK1,k1_yellow_0(sK0,X0)),sK2) )
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(resolution,[],[f202,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',t2_subset)).

fof(f202,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK1,k1_yellow_0(sK0,X0)),sK2)
        | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(resolution,[],[f133,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,X1))
        | m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK0,X1)),X2) )
    | ~ spl7_0 ),
    inference(resolution,[],[f106,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',t4_subset)).

fof(f106,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK3(sK0,X8,k1_yellow_0(sK0,X9)),X8)
        | r2_lattice3(sK0,X8,k1_yellow_0(sK0,X9)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f100,f71])).

fof(f100,plain,
    ( ! [X8,X9] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK3(sK0,X8,k1_yellow_0(sK0,X9)),X8)
        | r2_lattice3(sK0,X8,k1_yellow_0(sK0,X9)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f257,plain,
    ( ~ spl7_0
    | ~ spl7_4
    | spl7_11
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f93,f255])).

fof(f255,plain,
    ( ! [X0] : r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,X0))
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f254,f80])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,sK1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f251,f73])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,sK1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,X0)) )
    | ~ spl7_0
    | ~ spl7_30 ),
    inference(resolution,[],[f195,f102])).

fof(f195,plain,
    ( ! [X0] : r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_30
  <=> ! [X0] : r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f196,plain,
    ( ~ spl7_29
    | spl7_30
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f179,f88,f70,f194,f191])).

fof(f179,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X0))
        | ~ v1_xboole_0(sK2) )
    | ~ spl7_0
    | ~ spl7_8 ),
    inference(resolution,[],[f134,f89])).

fof(f134,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(X5))
        | r2_lattice3(sK0,X3,k1_yellow_0(sK0,X4))
        | ~ v1_xboole_0(X5) )
    | ~ spl7_0 ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',t5_subset)).

fof(f155,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f128,f83,f70,f153])).

fof(f83,plain,
    ( spl7_6
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f128,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl7_0
    | ~ spl7_6 ),
    inference(resolution,[],[f103,f84])).

fof(f84,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f97,f71])).

fof(f97,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & r1_tarski(X1,X2) )
           => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',t34_yellow_0)).

fof(f90,plain,
    ( spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f86,f75,f88])).

fof(f75,plain,
    ( spl7_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t34_yellow_0.p',t3_subset)).

fof(f76,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f46,f70])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
