%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1532+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 486 expanded)
%              Number of leaves         :   15 ( 155 expanded)
%              Depth                    :   24
%              Number of atoms          :  610 (3663 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f74,f75,f76,f80,f81,f82,f246,f328])).

fof(f328,plain,
    ( spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f324,f61])).

fof(f61,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_2
  <=> r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f324,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(resolution,[],[f277,f281])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f280,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_yellow_0)).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f279,f29])).

fof(f29,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f262,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f262,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,sK5(sK0,X2,X3),sK3)
        | ~ r2_hidden(sK5(sK0,X2,X3),sK1)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f260,f28])).

fof(f260,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK0,X2,X3),sK1)
        | r1_orders_2(sK0,sK5(sK0,X2,X3),sK3)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f252,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f251,f28])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f250,f29])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_6
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f277,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f276,f28])).

fof(f276,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f274,f29])).

fof(f274,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl7_5 ),
    inference(resolution,[],[f271,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,k2_xboole_0(X1,X2),X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,k2_xboole_0(X1,X2),X3),X1)
      | r2_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ),
    inference(resolution,[],[f45,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f270,f28])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f269,f29])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f257,f46])).

fof(f257,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,sK5(sK0,X2,X3),sK3)
        | ~ r2_hidden(sK5(sK0,X2,X3),sK2)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f255,f28])).

fof(f255,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK0,X2,X3),sK2)
        | r1_orders_2(sK0,sK5(sK0,X2,X3),sK3)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f249,f44])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f248,f28])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f247,f29])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f73,f43])).

fof(f73,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_5
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f246,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f58,plain,
    ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f242,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f215,f219])).

% (4025)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f218,f28])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f217,f29])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f125,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f125,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK4(sK0,X0,X1),sK1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f119,f28])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,X0,X1),sK1)
        | r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f96,f40])).

% (4030)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | r1_orders_2(sK0,sK3,X1) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f95,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X1)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f39,f69])).

fof(f69,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_4
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f215,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f214,f28])).

fof(f214,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f212,f29])).

fof(f212,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f183,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,k2_xboole_0(X1,X2),X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,k2_xboole_0(X1,X2),X3),X1)
      | r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ),
    inference(resolution,[],[f41,f55])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f182,f28])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f181,f29])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f116,f42])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK4(sK0,X0,X1),sK2)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f107,f28])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,X0,X1),sK2)
        | r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f94,f40])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f91,f29])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f39,f65])).

fof(f65,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f82,plain,
    ( spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f30,f78,f68])).

fof(f30,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f31,f78,f64])).

fof(f31,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,
    ( ~ spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f32,f78,f57])).

fof(f32,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f33,f72,f68])).

fof(f33,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f34,f72,f64])).

% (4025)Refutation not found, incomplete strategy% (4025)------------------------------
% (4025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4025)Termination reason: Refutation not found, incomplete strategy

% (4025)Memory used [KB]: 10618
% (4025)Time elapsed: 0.079 s
% (4025)------------------------------
% (4025)------------------------------
fof(f34,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f35,f72,f57])).

fof(f35,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f36,f60,f68])).

fof(f36,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f37,f60,f64])).

fof(f37,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f60,f57])).

fof(f38,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
