%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t26_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 816 expanded)
%              Number of leaves         :   14 ( 269 expanded)
%              Depth                    :   30
%              Number of atoms          :  680 (4361 expanded)
%              Number of equality atoms :  114 (1370 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f136,f1033])).

fof(f1033,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1031,f60])).

fof(f60,plain,(
    k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    & r1_yellow_0(sK0,sK2)
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(sK0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(sK0,X2) )
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( k1_yellow_0(sK1,X2) != k1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X2) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
          & r1_yellow_0(X0,X2) )
     => ( k1_yellow_0(X0,sK2) != k1_yellow_0(X1,sK2)
        & r1_yellow_0(X0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
              & r1_yellow_0(X0,X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( r1_yellow_0(X0,X2)
                 => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',t26_yellow_0)).

fof(f1031,plain,
    ( k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f1030,f59])).

fof(f59,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1030,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1029,f311])).

fof(f311,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f310,f56])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f310,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_yellow_0(sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ r1_yellow_0(X2,X3)
      | r1_yellow_0(sK1,X3)
      | ~ l1_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f57,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X3] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | ~ r1_yellow_0(X2,X3)
      | r1_yellow_0(sK1,X3)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X2) ) ),
    inference(superposition,[],[f63,f58])).

fof(f58,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_yellow_0(X0,X2)
      | r1_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',t14_yellow_0)).

fof(f1029,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ r1_yellow_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f1021,f603])).

fof(f603,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f601,f182])).

fof(f182,plain,
    ( ! [X8] : m1_subset_1(k1_yellow_0(sK1,X8),u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f165,plain,
    ( ! [X8] :
        ( m1_subset_1(k1_yellow_0(sK1,X8),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1) )
    | ~ spl7_2 ),
    inference(superposition,[],[f75,f156])).

fof(f156,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,
    ( ! [X35,X34] :
        ( g1_orders_2(X34,X35) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X34 )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_2
  <=> ! [X34,X35] :
        ( g1_orders_2(X34,X35) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X34 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',dt_k1_yellow_0)).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f600,f299])).

fof(f299,plain,
    ( ! [X35] :
        ( r2_lattice3(sK1,X35,k1_yellow_0(sK1,X35))
        | ~ r1_yellow_0(sK1,X35) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f205,f182])).

fof(f205,plain,
    ( ! [X35] :
        ( ~ m1_subset_1(k1_yellow_0(sK1,X35),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK1,X35)
        | r2_lattice3(sK1,X35,k1_yellow_0(sK1,X35)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f175,f57])).

fof(f175,plain,
    ( ! [X35] :
        ( ~ m1_subset_1(k1_yellow_0(sK1,X35),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK1,X35)
        | r2_lattice3(sK1,X35,k1_yellow_0(sK1,X35))
        | ~ l1_orders_2(sK1) )
    | ~ spl7_2 ),
    inference(superposition,[],[f89,f156])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',d9_yellow_0)).

fof(f600,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f589,f56])).

fof(f589,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X1,X0)
        | r2_lattice3(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f588])).

fof(f588,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f542])).

fof(f542,plain,
    ( ! [X28,X26,X27] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
        | ~ m1_subset_1(X28,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | r2_lattice3(X26,X27,X28)
        | ~ l1_orders_2(X26) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f118,f156])).

fof(f118,plain,(
    ! [X28,X26,X27] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
      | ~ r2_lattice3(sK1,X27,X28)
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(sK1))
      | r2_lattice3(X26,X27,X28)
      | ~ l1_orders_2(X26) ) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,(
    ! [X28,X26,X27] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X26),u1_orders_2(X26))
      | ~ r2_lattice3(sK1,X27,X28)
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(sK1))
      | r2_lattice3(X26,X27,X28)
      | ~ l1_orders_2(X26)
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f87,f58])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',t2_yellow_0)).

fof(f1021,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1020,f609])).

fof(f609,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f608,f311])).

fof(f608,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK1,X0)
        | m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f607,f56])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK1,X0)
        | m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f606,f182])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK1,X0)
        | m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f603,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1020,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1019,f311])).

fof(f1019,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK1,X0)
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f1018])).

fof(f1018,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0,k1_yellow_0(sK1,X0)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK1,X0)
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0)
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f763,f814])).

fof(f814,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK3(sK0,X0,k1_yellow_0(sK1,X0)))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f813,f182])).

fof(f813,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK3(sK0,X0,k1_yellow_0(sK1,X0)))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f812])).

fof(f812,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,X0,sK3(sK0,X0,k1_yellow_0(sK1,X0)))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK1,X0))
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X0) = k1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f629,f609])).

fof(f629,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3(sK0,X1,X2),u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,sK3(sK0,X1,X2))
        | k1_yellow_0(sK0,X1) = X2
        | ~ r2_lattice3(sK0,X1,X2)
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f628,f56])).

fof(f628,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3(sK0,X1,X2),u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,sK3(sK0,X1,X2))
        | k1_yellow_0(sK0,X1) = X2
        | ~ r2_lattice3(sK0,X1,X2)
        | ~ r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f626,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f626,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f615,f56])).

fof(f615,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f614])).

fof(f614,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f545])).

fof(f545,plain,
    ( ! [X30,X31,X29] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X29),u1_orders_2(X29))
        | ~ m1_subset_1(X31,u1_struct_0(sK0))
        | ~ r2_lattice3(X29,X30,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | r2_lattice3(sK1,X30,X31)
        | ~ l1_orders_2(X29) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f119,f156])).

fof(f119,plain,(
    ! [X30,X31,X29] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X29),u1_orders_2(X29))
      | ~ r2_lattice3(X29,X30,X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK1))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | r2_lattice3(sK1,X30,X31)
      | ~ l1_orders_2(X29) ) ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f103,plain,(
    ! [X30,X31,X29] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X29),u1_orders_2(X29))
      | ~ r2_lattice3(X29,X30,X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK1))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | r2_lattice3(sK1,X30,X31)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X29) ) ),
    inference(superposition,[],[f87,f58])).

fof(f763,plain,
    ( ! [X2,X3] :
        ( ~ r2_lattice3(sK1,X2,sK3(sK0,X3,k1_yellow_0(sK1,X2)))
        | ~ m1_subset_1(sK3(sK0,X3,k1_yellow_0(sK1,X2)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK1,X2)
        | k1_yellow_0(sK0,X3) = k1_yellow_0(sK1,X2)
        | ~ r2_lattice3(sK0,X3,k1_yellow_0(sK1,X2))
        | ~ r1_yellow_0(sK0,X3) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f762,f56])).

fof(f762,plain,
    ( ! [X2,X3] :
        ( ~ r1_yellow_0(sK1,X2)
        | ~ m1_subset_1(sK3(sK0,X3,k1_yellow_0(sK1,X2)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X2,sK3(sK0,X3,k1_yellow_0(sK1,X2)))
        | k1_yellow_0(sK0,X3) = k1_yellow_0(sK1,X2)
        | ~ r2_lattice3(sK0,X3,k1_yellow_0(sK1,X2))
        | ~ r1_yellow_0(sK0,X3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f760,f182])).

fof(f760,plain,
    ( ! [X2,X3] :
        ( ~ r1_yellow_0(sK1,X2)
        | ~ m1_subset_1(sK3(sK0,X3,k1_yellow_0(sK1,X2)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X2,sK3(sK0,X3,k1_yellow_0(sK1,X2)))
        | k1_yellow_0(sK0,X3) = k1_yellow_0(sK1,X2)
        | ~ r2_lattice3(sK0,X3,k1_yellow_0(sK1,X2))
        | ~ r1_yellow_0(sK0,X3)
        | ~ m1_subset_1(k1_yellow_0(sK1,X2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f755,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f755,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k1_yellow_0(sK1,X0),X1)
        | ~ r1_yellow_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f754,f182])).

fof(f754,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,X0,X1)
        | ~ r1_yellow_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK1,X0),X1) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f752])).

fof(f752,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,X0,X1)
        | ~ r1_yellow_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,k1_yellow_0(sK1,X0),X1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f751,f723])).

fof(f723,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f708,f56])).

fof(f708,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X1,X0)
        | r1_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f707])).

fof(f707,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_2 ),
    inference(equality_resolution,[],[f648])).

fof(f648,plain,
    ( ! [X14,X15,X16] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | r1_orders_2(X14,X15,X16)
        | ~ l1_orders_2(X14) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f647,f156])).

fof(f647,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_subset_1(X16,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
        | ~ r1_orders_2(sK1,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ m1_subset_1(X15,u1_struct_0(sK1))
        | r1_orders_2(X14,X15,X16)
        | ~ l1_orders_2(X14) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f114,f156])).

fof(f114,plain,(
    ! [X14,X15,X16] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
      | ~ r1_orders_2(sK1,X15,X16)
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ m1_subset_1(X15,u1_struct_0(sK1))
      | r1_orders_2(X14,X15,X16)
      | ~ l1_orders_2(X14) ) ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f98,plain,(
    ! [X14,X15,X16] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X14),u1_orders_2(X14))
      | ~ r1_orders_2(sK1,X15,X16)
      | ~ m1_subset_1(X16,u1_struct_0(X14))
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ m1_subset_1(X15,u1_struct_0(sK1))
      | r1_orders_2(X14,X15,X16)
      | ~ l1_orders_2(X14)
      | ~ l1_orders_2(sK1) ) ),
    inference(superposition,[],[f85,f58])).

fof(f85,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',t1_yellow_0)).

fof(f751,plain,
    ( ! [X33,X34] :
        ( r1_orders_2(sK1,k1_yellow_0(sK1,X33),X34)
        | ~ r2_lattice3(sK1,X33,X34)
        | ~ r1_yellow_0(sK1,X33)
        | ~ m1_subset_1(X34,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f204,f182])).

fof(f204,plain,
    ( ! [X33,X34] :
        ( ~ m1_subset_1(X34,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK1,X33),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X33,X34)
        | ~ r1_yellow_0(sK1,X33)
        | r1_orders_2(sK1,k1_yellow_0(sK1,X33),X34) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f203,f156])).

fof(f203,plain,
    ( ! [X33,X34] :
        ( ~ m1_subset_1(k1_yellow_0(sK1,X33),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(sK1))
        | ~ r1_yellow_0(sK1,X33)
        | r1_orders_2(sK1,k1_yellow_0(sK1,X33),X34) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f174,plain,
    ( ! [X33,X34] :
        ( ~ m1_subset_1(k1_yellow_0(sK1,X33),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(sK1))
        | ~ r1_yellow_0(sK1,X33)
        | r1_orders_2(sK1,k1_yellow_0(sK1,X33),X34)
        | ~ l1_orders_2(sK1) )
    | ~ spl7_2 ),
    inference(superposition,[],[f88,f156])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f136,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f134,f57])).

fof(f134,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',dt_u1_orders_2)).

fof(f125,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_1
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f129,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f105,f127,f124])).

fof(f105,plain,(
    ! [X35,X34] :
      ( g1_orders_2(X34,X35) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X34
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f78,f58])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t26_yellow_0.p',free_g1_orders_2)).
%------------------------------------------------------------------------------
