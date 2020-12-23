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
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 498 expanded)
%              Number of leaves         :   15 ( 175 expanded)
%              Depth                    :   11
%              Number of atoms          :  394 (3771 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21765)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f80,f81,f86,f87,f88,f124,f257])).

fof(f257,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f188,f189,f126,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f126,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f29,f63,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f63,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl7_2
  <=> r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f29,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r2_lattice3(sK0,sK2,sK3)
        & r2_lattice3(sK0,sK1,sK3) )
      | ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r1_lattice3(sK0,sK2,sK3)
        & r1_lattice3(sK0,sK1,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
              | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X3,X2,X1] :
          ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(sK0,X2,X3)
              & r2_lattice3(sK0,X1,X3) )
            | ( ~ r1_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(sK0,X2,X3)
              & r1_lattice3(sK0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X3,X2,X1] :
        ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(X1,X2),X3)
            & r2_lattice3(sK0,X2,X3)
            & r2_lattice3(sK0,X1,X3) )
          | ( ~ r1_lattice3(sK0,k2_xboole_0(X1,X2),X3)
            & r1_lattice3(sK0,X2,X3)
            & r1_lattice3(sK0,X1,X3) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
          & r2_lattice3(sK0,sK2,sK3)
          & r2_lattice3(sK0,sK1,sK3) )
        | ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
          & r1_lattice3(sK0,sK2,sK3)
          & r1_lattice3(sK0,sK1,sK3) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X0))
           => ( ( ( r2_lattice3(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3) )
               => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
              & ( ( r1_lattice3(X0,X2,X3)
                  & r1_lattice3(X0,X1,X3) )
               => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X0))
         => ( ( ( r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
             => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
            & ( ( r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) )
             => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_yellow_0)).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f189,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f28,f85,f29,f125,f127,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f127,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK3)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f29,f63,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,
    ( m1_subset_1(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f28,f29,f63,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_6
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f188,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | spl7_2
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f28,f78,f29,f125,f127,f43])).

fof(f78,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_5
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f124,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f98,f99,f90,f55])).

fof(f90,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f28,f29,f59,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f59,plain,
    ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f99,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | spl7_1
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f28,f73,f29,f89,f91,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4(sK0,k2_xboole_0(sK1,sK2),sK3))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f28,f29,f59,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f28,f29,f59,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_4
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f98,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f28,f68,f29,f89,f91,f39])).

fof(f68,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f88,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f30,f83,f71])).

fof(f30,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f31,f83,f66])).

fof(f31,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,
    ( ~ spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f32,f83,f57])).

fof(f32,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f33,f76,f71])).

fof(f33,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f34,f76,f66])).

fof(f34,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f35,f76,f57])).

fof(f35,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f36,f61,f71])).

fof(f36,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f37,f61,f66])).

fof(f37,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f61,f57])).

fof(f38,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21759)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (21776)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (21768)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (21763)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (21774)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (21770)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (21768)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (21775)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (21762)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (21760)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (21758)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (21758)Refutation not found, incomplete strategy% (21758)------------------------------
% 0.22/0.50  % (21758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21758)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21758)Memory used [KB]: 10618
% 0.22/0.50  % (21758)Time elapsed: 0.082 s
% 0.22/0.50  % (21758)------------------------------
% 0.22/0.50  % (21758)------------------------------
% 0.22/0.50  % (21771)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  % (21765)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f80,f81,f86,f87,f88,f124,f257])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    spl7_2 | ~spl7_5 | ~spl7_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    $false | (spl7_2 | ~spl7_5 | ~spl7_6)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f188,f189,f126,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK6(X0,X1,X2),X1) & ~r2_hidden(sK6(X0,X1,X2),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK6(X0,X1,X2),X1) & ~r2_hidden(sK6(X0,X1,X2),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(rectify,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2)) | spl7_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f63,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(rectify,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) | spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl7_2 <=> r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    (((~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) & r2_lattice3(sK0,sK2,sK3) & r2_lattice3(sK0,sK1,sK3)) | (~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) & r1_lattice3(sK0,sK2,sK3) & r1_lattice3(sK0,sK1,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f13,f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | (~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X3,X2,X1] : (((~r2_lattice3(sK0,k2_xboole_0(X1,X2),X3) & r2_lattice3(sK0,X2,X3) & r2_lattice3(sK0,X1,X3)) | (~r1_lattice3(sK0,k2_xboole_0(X1,X2),X3) & r1_lattice3(sK0,X2,X3) & r1_lattice3(sK0,X1,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X3,X2,X1] : (((~r2_lattice3(sK0,k2_xboole_0(X1,X2),X3) & r2_lattice3(sK0,X2,X3) & r2_lattice3(sK0,X1,X3)) | (~r1_lattice3(sK0,k2_xboole_0(X1,X2),X3) & r1_lattice3(sK0,X2,X3) & r1_lattice3(sK0,X1,X3))) & m1_subset_1(X3,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) & r2_lattice3(sK0,sK2,sK3) & r2_lattice3(sK0,sK1,sK3)) | (~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) & r1_lattice3(sK0,sK2,sK3) & r1_lattice3(sK0,sK1,sK3))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | (~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & (r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3))) | (~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & (r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)))) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) => r2_lattice3(X0,k2_xboole_0(X1,X2),X3)) & ((r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) => r1_lattice3(X0,k2_xboole_0(X1,X2),X3)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) => r2_lattice3(X0,k2_xboole_0(X1,X2),X3)) & ((r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) => r1_lattice3(X0,k2_xboole_0(X1,X2),X3)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_yellow_0)).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK1) | (spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f85,f29,f125,f127,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~r1_orders_2(sK0,sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK3) | spl7_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f63,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    m1_subset_1(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0)) | spl7_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f63,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK1,sK3) | ~spl7_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl7_6 <=> r2_lattice3(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ~r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),sK3),sK2) | (spl7_2 | ~spl7_5)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f78,f29,f125,f127,f43])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK2,sK3) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl7_5 <=> r2_lattice3(sK0,sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl7_1 | ~spl7_3 | ~spl7_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    $false | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f98,f99,f90,f55])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2)) | spl7_1),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f59,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(rectify,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl7_1 <=> r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1) | (spl7_1 | ~spl7_4)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f73,f29,f89,f91,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~r1_orders_2(sK0,sK3,sK4(sK0,k2_xboole_0(sK1,sK2),sK3)) | spl7_1),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f59,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0)) | spl7_1),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f29,f59,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    r1_lattice3(sK0,sK1,sK3) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl7_4 <=> r1_lattice3(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2) | (spl7_1 | ~spl7_3)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f28,f68,f29,f89,f91,f39])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    r1_lattice3(sK0,sK2,sK3) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl7_3 <=> r1_lattice3(sK0,sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl7_4 | spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f83,f71])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl7_3 | spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f83,f66])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~spl7_1 | spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f83,f57])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK1,sK3) | ~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl7_4 | spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f76,f71])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl7_3 | spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f76,f66])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~spl7_1 | spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f76,f57])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl7_4 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f61,f71])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) | r1_lattice3(sK0,sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl7_3 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f61,f66])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) | r1_lattice3(sK0,sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~spl7_1 | ~spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f61,f57])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) | ~r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (21768)------------------------------
% 0.22/0.50  % (21768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21768)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (21768)Memory used [KB]: 10746
% 0.22/0.50  % (21768)Time elapsed: 0.079 s
% 0.22/0.50  % (21768)------------------------------
% 0.22/0.50  % (21768)------------------------------
% 0.22/0.50  % (21761)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (21772)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (21756)Success in time 0.143 s
%------------------------------------------------------------------------------
