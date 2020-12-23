%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1527+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 639 expanded)
%              Number of leaves         :   16 ( 216 expanded)
%              Depth                    :   12
%              Number of atoms          :  477 (5851 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f92,f93,f94,f210,f273,f335,f407])).

fof(f407,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f38,f86,f354,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f354,plain,
    ( ! [X0] : ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),k3_xboole_0(sK1,X0))
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f346,f74])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f346,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),sK1)
    | spl6_3
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f89,f38,f336,f338,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f338,plain,
    ( ~ r1_orders_2(sK0,sK2,sK4(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f37,f38,f86,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f336,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),u1_struct_0(sK0))
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f37,f38,f86,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_4
  <=> r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f86,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_3
  <=> r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r1_lattice3(sK0,sK1,sK2)
        & r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) )
      | ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
        & r1_lattice3(sK0,sK1,sK2) )
      | ( ~ r2_lattice3(sK0,sK1,sK2)
        & r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) )
      | ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
        & r2_lattice3(sK0,sK1,sK2) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ( ~ r1_lattice3(sK0,X1,X2)
              & r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2) )
            | ( ~ r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2)
              & r1_lattice3(sK0,X1,X2) )
            | ( ~ r2_lattice3(sK0,X1,X2)
              & r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2) )
            | ( ~ r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2)
              & r2_lattice3(sK0,X1,X2) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2,X1] :
        ( ( ( ~ r1_lattice3(sK0,X1,X2)
            & r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2) )
          | ( ~ r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2)
            & r1_lattice3(sK0,X1,X2) )
          | ( ~ r2_lattice3(sK0,X1,X2)
            & r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2) )
          | ( ~ r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),X2)
            & r2_lattice3(sK0,X1,X2) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ~ r1_lattice3(sK0,sK1,sK2)
          & r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) )
        | ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
          & r1_lattice3(sK0,sK1,sK2) )
        | ( ~ r2_lattice3(sK0,sK1,sK2)
          & r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) )
        | ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
          & r2_lattice3(sK0,sK1,sK2) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f335,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f275,f282,f287,f72])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f287,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f77,f38,f274,f276,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f276,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK2),sK2)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f38,f82,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f274,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f38,f82,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_1
  <=> r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f282,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f96,f274,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f96,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f95,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f95,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f275,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f38,f82,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f273,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f212,f220,f221,f72])).

fof(f221,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2),k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl6_3
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f85,f38,f211,f213,f60])).

fof(f213,plain,
    ( ~ r1_orders_2(sK0,sK2,sK4(sK0,sK1,sK2))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f38,f90,f63])).

fof(f90,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f211,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f38,f90,f61])).

fof(f85,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f220,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f96,f211,f65])).

fof(f212,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK1)
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f37,f38,f90,f62])).

fof(f210,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f38,f78,f125,f58])).

fof(f125,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),k3_xboole_0(sK1,X0))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f121,f74])).

fof(f121,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),sK1)
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f37,f81,f38,f100,f102,f56])).

fof(f102,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),sK2)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f38,f78,f59])).

fof(f100,plain,
    ( m1_subset_1(sK3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2),u1_struct_0(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f37,f38,f78,f57])).

fof(f81,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f78,plain,
    ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f94,plain,
    ( spl6_2
    | spl6_1
    | spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f39,f84,f88,f76,f80])).

fof(f39,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f42,f84,f88,f80,f76])).

fof(f42,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r1_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,
    ( spl6_2
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f51,f88,f84,f76,f80])).

fof(f51,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f54,f88,f84,f80,f76])).

fof(f54,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
