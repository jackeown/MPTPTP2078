%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t49_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:44 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 411 expanded)
%              Number of leaves         :   17 ( 121 expanded)
%              Depth                    :   21
%              Number of atoms          :  579 (3136 expanded)
%              Number of equality atoms :   43 ( 339 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f109,f171,f181,f198,f210,f220,f227])).

fof(f227,plain,
    ( ~ spl7_11
    | ~ spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f223,f179,f225,f145])).

fof(f145,plain,
    ( spl7_11
  <=> ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f225,plain,
    ( spl7_13
  <=> ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f179,plain,
    ( spl7_1
  <=> ~ r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f223,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f222,f55])).

fof(f55,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2)
    & ! [X3] :
        ( ( ( r1_lattice3(sK0,sK1,X3)
            | ~ r1_lattice3(sK0,sK2,X3) )
          & ( r1_lattice3(sK0,sK2,X3)
            | ~ r1_lattice3(sK0,sK1,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & r2_yellow_0(sK0,sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
            & ! [X3] :
                ( ( ( r1_lattice3(X0,X1,X3)
                    | ~ r1_lattice3(X0,X2,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,X2)
          & ! [X3] :
              ( ( ( r1_lattice3(sK0,X1,X3)
                  | ~ r1_lattice3(sK0,X2,X3) )
                & ( r1_lattice3(sK0,X2,X3)
                  | ~ r1_lattice3(sK0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & r2_yellow_0(sK0,X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
     => ( k2_yellow_0(X0,sK1) != k2_yellow_0(X0,sK2)
        & ! [X3] :
            ( ( ( r1_lattice3(X0,sK1,X3)
                | ~ r1_lattice3(X0,sK2,X3) )
              & ( r1_lattice3(X0,sK2,X3)
                | ~ r1_lattice3(X0,sK1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_yellow_0(X0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) )
              & r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t49_yellow_0.p',t49_yellow_0)).

fof(f222,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f221,f58])).

fof(f58,plain,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f221,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f201,f54])).

fof(f54,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f201,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f154,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,X0)
      | k2_yellow_0(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | k2_yellow_0(sK0,sK1) = X0
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | k2_yellow_0(sK0,sK1) = X0
      | ~ r2_yellow_0(sK0,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | k2_yellow_0(sK0,sK1) = X0
      | k2_yellow_0(sK0,sK1) = X0
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ r2_yellow_0(sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f113,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t49_yellow_0.p',d10_yellow_0)).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | k2_yellow_0(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f112,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,sK1) = X0
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | ~ m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f110,f55])).

fof(f110,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,sK1) = X0
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ r2_yellow_0(sK0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_lattice3(sK0,sK2,sK3(sK0,sK1,X0))
      | ~ m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK0,sK1,X3)
      | r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK3(X0,X1,k2_yellow_0(X0,X2)))
      | ~ r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f153,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t49_yellow_0.p',dt_k2_yellow_0)).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK3(X0,X1,k2_yellow_0(X0,X2)))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f152,f62])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X0,X1,k2_yellow_0(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK3(X0,X1,k2_yellow_0(X0,X2)))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(X0,X1,k2_yellow_0(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK3(X0,X1,k2_yellow_0(X0,X2)))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f117,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f76,f69])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f220,plain,
    ( spl7_1
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f218,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f218,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f217,f54])).

fof(f217,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f216,f189])).

fof(f189,plain,
    ( r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f188,f55])).

fof(f188,plain,
    ( r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ spl7_4 ),
    inference(factoring,[],[f108])).

fof(f108,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f216,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f215,f180])).

fof(f180,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f215,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f214,f55])).

fof(f214,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f197,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK4(X0,X1,X2))
              | r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK4(X0,X1,X2))
          | r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t49_yellow_0.p',t48_yellow_0)).

fof(f197,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_22
  <=> r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f210,plain,
    ( spl7_1
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f208,f53])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f207,f54])).

fof(f207,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f206,f180])).

fof(f206,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f205,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_21 ),
    inference(resolution,[],[f194,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f194,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_21
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f198,plain,
    ( ~ spl7_21
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f191,f107,f196,f193])).

fof(f191,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f189,f56])).

fof(f181,plain,
    ( ~ spl7_11
    | spl7_12
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f177,f179,f148,f145])).

fof(f148,plain,
    ( spl7_12
  <=> r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f177,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f132,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK0,sK2,X3)
      | r1_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f77,f69])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f171,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f169,f54])).

fof(f169,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_11 ),
    inference(resolution,[],[f146,f69])).

fof(f146,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f109,plain,
    ( spl7_0
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f105,f96,f107,f93])).

fof(f93,plain,
    ( spl7_0
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f96,plain,
    ( spl7_2
  <=> ! [X1] :
        ( ~ r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK4(sK0,X1,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,sK4(sK0,X1,sK2))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | r2_yellow_0(sK0,sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f104,f53])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | r2_yellow_0(sK0,sK2)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f103,f54])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | r2_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2))
        | r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | ~ r2_yellow_0(sK0,X0)
        | r2_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f97,f65])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1,sK2),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X1)
        | r1_lattice3(sK0,sK1,sK4(sK0,X1,sK2))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,sK2)) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl7_0
    | spl7_2 ),
    inference(avatar_split_clause,[],[f91,f96,f93])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK0,X1)
      | r2_yellow_0(sK0,sK2)
      | r1_lattice3(sK0,X1,sK4(sK0,X1,sK2))
      | r1_lattice3(sK0,sK1,sK4(sK0,X1,sK2))
      | ~ m1_subset_1(sK4(sK0,X1,sK2),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f90,f53])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK0,X1)
      | r2_yellow_0(sK0,sK2)
      | r1_lattice3(sK0,X1,sK4(sK0,X1,sK2))
      | v2_struct_0(sK0)
      | r1_lattice3(sK0,sK1,sK4(sK0,X1,sK2))
      | ~ m1_subset_1(sK4(sK0,X1,sK2),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f88,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK0,X1)
      | r2_yellow_0(sK0,sK2)
      | r1_lattice3(sK0,X1,sK4(sK0,X1,sK2))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_lattice3(sK0,sK1,sK4(sK0,X1,sK2))
      | ~ m1_subset_1(sK4(sK0,X1,sK2),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
