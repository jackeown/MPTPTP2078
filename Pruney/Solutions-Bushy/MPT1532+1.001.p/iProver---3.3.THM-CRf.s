%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1532+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:48 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  222 (2283 expanded)
%              Number of clauses        :  173 ( 607 expanded)
%              Number of leaves         :   10 ( 575 expanded)
%              Depth                    :   26
%              Number of atoms          :  974 (13997 expanded)
%              Number of equality atoms :  379 ( 934 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
        & r1_lattice3(X0,X2,X3)
        & r1_lattice3(X0,X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | sP0(X3,X2,X1,X0) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f11,f12])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | sP0(X3,X2,X1,X0) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,k2_xboole_0(sK5,sK6),sK7)
            & r2_lattice3(X0,sK6,sK7)
            & r2_lattice3(X0,sK5,sK7) )
          | sP0(sK7,sK6,sK5,X0) )
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
              | sP0(X3,X2,X1,X0) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X3,X2,X1] :
          ( ( ( ~ r2_lattice3(sK4,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(sK4,X2,X3)
              & r2_lattice3(sK4,X1,X3) )
            | sP0(X3,X2,X1,sK4) )
          & m1_subset_1(X3,u1_struct_0(sK4)) )
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
        & r2_lattice3(sK4,sK6,sK7)
        & r2_lattice3(sK4,sK5,sK7) )
      | sP0(sK7,sK6,sK5,sK4) )
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f30,f29])).

fof(f49,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
        & r1_lattice3(X0,X2,X3)
        & r1_lattice3(X0,X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_lattice3(X3,k2_xboole_0(X2,X1),X0)
        & r1_lattice3(X3,X1,X0)
        & r1_lattice3(X3,X2,X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f27])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X3,k2_xboole_0(X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | sP0(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | sP0(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X3,X2,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | sP0(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X3,X1,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_429,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_430,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ r1_lattice3(sK4,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_3694,plain,
    ( r1_orders_2(sK4,X0,sK2(X1,k2_xboole_0(sK5,sK6),sK7))
    | ~ r1_lattice3(sK4,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(X1,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ r2_hidden(sK2(X1,k2_xboole_0(sK5,sK6),sK7),X2) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_4071,plain,
    ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
    | ~ r1_lattice3(sK4,X1,sK7)
    | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),X1) ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_8610,plain,
    ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
    | ~ r1_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_8611,plain,
    ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) != iProver_top
    | m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8610])).

cnf(c_8613,plain,
    ( r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) != iProver_top
    | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8611])).

cnf(c_8605,plain,
    ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
    | ~ r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_8606,plain,
    ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top
    | m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8605])).

cnf(c_8608,plain,
    ( r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top
    | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8606])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_465,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_466,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_2217,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2234,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2712,plain,
    ( r1_lattice3(sK4,k2_xboole_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_2234])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_450,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_451,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_2218,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_2219,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_3022,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1,X2)) = iProver_top
    | r1_lattice3(sK4,X3,X0) != iProver_top
    | r1_lattice3(sK4,X1,X2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X1,X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_2219])).

cnf(c_4050,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,k2_xboole_0(X1,X2),X3)) = iProver_top
    | r1_lattice3(sK4,X2,X0) != iProver_top
    | r1_lattice3(sK4,k2_xboole_0(X1,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(X1,X2),X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_3022])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_480,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_481,plain,
    ( ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
    | r1_lattice3(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_2216,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1,X0)) != iProver_top
    | r1_lattice3(sK4,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_6712,plain,
    ( r1_lattice3(sK4,X0,X1) != iProver_top
    | r1_lattice3(sK4,k2_xboole_0(X2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(X2,X0),X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4050,c_2216])).

cnf(c_6817,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,k2_xboole_0(X1,X2),X3)) = iProver_top
    | r1_lattice3(sK4,X2,X3) != iProver_top
    | r1_lattice3(sK4,X1,X0) != iProver_top
    | r1_lattice3(sK4,k2_xboole_0(X1,X2),X3) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6712,c_3022])).

cnf(c_7004,plain,
    ( r1_lattice3(sK4,X0,X1) != iProver_top
    | r1_lattice3(sK4,X2,X1) != iProver_top
    | r1_lattice3(sK4,k2_xboole_0(X2,X0),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6817,c_2216])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_lattice3(X3,k2_xboole_0(X2,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( sP0(sK7,sK6,sK5,sK4)
    | r2_lattice3(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_316,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
    | sK7 != X3
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_317,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_2225,plain,
    ( r2_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_7850,plain,
    ( r2_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7004,c_2225])).

cnf(c_19,negated_conjecture,
    ( sP0(sK7,sK6,sK5,sK4)
    | r2_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_306,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
    | sK7 != X3
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_307,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_2226,plain,
    ( r2_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_7849,plain,
    ( r2_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7004,c_2226])).

cnf(c_4633,plain,
    ( r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0)
    | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(X0,sK6))
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6129,plain,
    ( ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6)
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_4633])).

cnf(c_6130,plain,
    ( r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6129])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_399,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_400,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_2221,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_3310,plain,
    ( r2_lattice3(sK4,k2_xboole_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_2234])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_384,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_385,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_2222,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_lattice3(X3,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_256,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_257,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | r1_lattice3(sK4,sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_2231,plain,
    ( r2_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_363,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_364,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_2223,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_2929,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_2223])).

cnf(c_1604,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X2)
    | sK7 != X1
    | sK6 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_364])).

cnf(c_1605,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_1604])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1609,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattice3(sK4,sK5,sK7)
    | r1_orders_2(sK4,X0,sK7)
    | ~ r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_20])).

cnf(c_1610,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(renaming,[status(thm)],[c_1609])).

cnf(c_1611,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1610])).

cnf(c_3486,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_orders_2(sK4,X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2929,c_1611])).

cnf(c_3487,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3486])).

cnf(c_3491,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_3487])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_414,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_415,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_2220,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_4322,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3491,c_2220])).

cnf(c_23,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4327,plain,
    ( r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_lattice3(sK4,X0,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_23])).

cnf(c_4328,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4327])).

cnf(c_4334,plain,
    ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_4328])).

cnf(c_5637,plain,
    ( r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4334,c_23])).

cnf(c_5638,plain,
    ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5637])).

cnf(c_5645,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK6,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5638,c_4328])).

cnf(c_17,negated_conjecture,
    ( sP0(sK7,sK6,sK5,sK4)
    | ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_266,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_17])).

cnf(c_267,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | r1_lattice3(sK4,sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_268,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_246,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_247,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(sK4,sK5,sK7) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_2232,plain,
    ( r2_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_3019,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2232,c_2223])).

cnf(c_1676,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X2)
    | sK7 != X1
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_364])).

cnf(c_1677,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_1676])).

cnf(c_1681,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_lattice3(sK4,sK5,sK7)
    | r1_orders_2(sK4,X0,sK7)
    | ~ r2_hidden(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1677,c_20])).

cnf(c_1682,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK5,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5) ),
    inference(renaming,[status(thm)],[c_1681])).

cnf(c_1683,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_3755,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_orders_2(sK4,X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3019,c_1683])).

cnf(c_3756,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_3755])).

cnf(c_3760,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_3756])).

cnf(c_4629,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_2220])).

cnf(c_4683,plain,
    ( r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_lattice3(sK4,X0,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4629,c_23])).

cnf(c_4684,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4683])).

cnf(c_5646,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5638,c_4684])).

cnf(c_5656,plain,
    ( r1_lattice3(sK4,sK5,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5645,c_268,c_5646])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_lattice3(X3,X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_286,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X1
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_287,plain,
    ( r2_lattice3(sK4,sK6,sK7)
    | r1_lattice3(sK4,sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_2228,plain,
    ( r2_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_2886,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2228,c_2223])).

cnf(c_1580,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X2)
    | sK7 != X1
    | sK6 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_287,c_364])).

cnf(c_1581,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_1580])).

cnf(c_1582,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1581])).

cnf(c_3361,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_orders_2(sK4,X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_23,c_1582])).

cnf(c_3362,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3361])).

cnf(c_3366,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_3362])).

cnf(c_3952,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_2220])).

cnf(c_3957,plain,
    ( r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_lattice3(sK4,X0,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3952,c_23])).

cnf(c_3958,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3957])).

cnf(c_3964,plain,
    ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3310,c_3958])).

cnf(c_5178,plain,
    ( r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3964,c_23])).

cnf(c_5179,plain,
    ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5178])).

cnf(c_5187,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK6,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_3958])).

cnf(c_296,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X1
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_297,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | r1_lattice3(sK4,sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_298,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_276,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(X0,X1,X2)
    | sK7 != X2
    | sK6 != X1
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_277,plain,
    ( r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(sK4,sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_2229,plain,
    ( r2_lattice3(sK4,sK5,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_2926,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2229,c_2223])).

cnf(c_1652,plain,
    ( r1_orders_2(sK4,X0,X1)
    | r1_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X2)
    | sK7 != X1
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_364])).

cnf(c_1653,plain,
    ( r1_orders_2(sK4,X0,sK7)
    | r1_lattice3(sK4,sK6,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_1652])).

cnf(c_1654,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1653])).

cnf(c_3422,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r1_orders_2(sK4,X0,sK7) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2926,c_23,c_1654])).

cnf(c_3423,plain,
    ( r1_orders_2(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_3422])).

cnf(c_3427,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_3423])).

cnf(c_3995,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_2220])).

cnf(c_4031,plain,
    ( r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_lattice3(sK4,X0,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3995,c_23])).

cnf(c_4032,plain,
    ( r2_lattice3(sK4,X0,sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4031])).

cnf(c_5189,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
    | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5179,c_4032])).

cnf(c_5199,plain,
    ( r1_lattice3(sK4,sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5187,c_298,c_5189])).

cnf(c_2651,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_2933,plain,
    ( ~ r2_lattice3(sK4,X0,sK7)
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
    | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0) ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_4111,plain,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
    | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_2933])).

cnf(c_4112,plain,
    ( r2_lattice3(sK4,sK5,sK7) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) = iProver_top
    | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4111])).

cnf(c_4108,plain,
    ( ~ r2_lattice3(sK4,sK6,sK7)
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
    | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_2933])).

cnf(c_4109,plain,
    ( r2_lattice3(sK4,sK6,sK7) != iProver_top
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) = iProver_top
    | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4108])).

cnf(c_3293,plain,
    ( r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),X0)
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),X1)
    | ~ r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3980,plain,
    ( ~ r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6))
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6)
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
    inference(instantiation,[status(thm)],[c_3293])).

cnf(c_3981,plain,
    ( r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) = iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3980])).

cnf(c_2305,plain,
    ( r2_lattice3(sK4,X0,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_2349,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2305])).

cnf(c_2350,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2349])).

cnf(c_2311,plain,
    ( r2_lattice3(sK4,X0,sK7)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,sK7),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_2346,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2311])).

cnf(c_2347,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_2289,plain,
    ( r2_lattice3(sK4,X0,sK7)
    | m1_subset_1(sK3(sK4,X0,sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_2341,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_2342,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
    | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2341])).

cnf(c_326,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
    | sK7 != X3
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_327,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_1022,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k2_xboole_0(sK5,sK6) != X1
    | sK7 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_481])).

cnf(c_1023,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1022])).

cnf(c_1024,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
    | r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_952,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
    | k2_xboole_0(sK5,sK6) != X1
    | sK7 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_451])).

cnf(c_953,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_954,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
    | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_938,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X1,X0),X1)
    | k2_xboole_0(sK5,sK6) != X1
    | sK7 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_466])).

cnf(c_939,plain,
    ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_940,plain,
    ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8613,c_8608,c_7850,c_7849,c_6130,c_5656,c_5199,c_4112,c_4109,c_3981,c_2350,c_2347,c_2342,c_1024,c_954,c_940,c_23])).


%------------------------------------------------------------------------------
