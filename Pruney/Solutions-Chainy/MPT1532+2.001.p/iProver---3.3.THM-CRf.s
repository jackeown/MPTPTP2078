%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:28 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.99  
% 4.00/0.99  ------  iProver source info
% 4.00/0.99  
% 4.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.99  git: non_committed_changes: false
% 4.00/0.99  git: last_make_outside_of_git: false
% 4.00/0.99  
% 4.00/0.99  ------ 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options
% 4.00/0.99  
% 4.00/0.99  --out_options                           all
% 4.00/0.99  --tptp_safe_out                         true
% 4.00/0.99  --problem_path                          ""
% 4.00/0.99  --include_path                          ""
% 4.00/0.99  --clausifier                            res/vclausify_rel
% 4.00/0.99  --clausifier_options                    ""
% 4.00/0.99  --stdin                                 false
% 4.00/0.99  --stats_out                             all
% 4.00/0.99  
% 4.00/0.99  ------ General Options
% 4.00/0.99  
% 4.00/0.99  --fof                                   false
% 4.00/0.99  --time_out_real                         305.
% 4.00/0.99  --time_out_virtual                      -1.
% 4.00/0.99  --symbol_type_check                     false
% 4.00/0.99  --clausify_out                          false
% 4.00/0.99  --sig_cnt_out                           false
% 4.00/0.99  --trig_cnt_out                          false
% 4.00/0.99  --trig_cnt_out_tolerance                1.
% 4.00/0.99  --trig_cnt_out_sk_spl                   false
% 4.00/0.99  --abstr_cl_out                          false
% 4.00/0.99  
% 4.00/0.99  ------ Global Options
% 4.00/0.99  
% 4.00/0.99  --schedule                              default
% 4.00/0.99  --add_important_lit                     false
% 4.00/0.99  --prop_solver_per_cl                    1000
% 4.00/0.99  --min_unsat_core                        false
% 4.00/0.99  --soft_assumptions                      false
% 4.00/0.99  --soft_lemma_size                       3
% 4.00/0.99  --prop_impl_unit_size                   0
% 4.00/0.99  --prop_impl_unit                        []
% 4.00/0.99  --share_sel_clauses                     true
% 4.00/0.99  --reset_solvers                         false
% 4.00/0.99  --bc_imp_inh                            [conj_cone]
% 4.00/0.99  --conj_cone_tolerance                   3.
% 4.00/0.99  --extra_neg_conj                        none
% 4.00/0.99  --large_theory_mode                     true
% 4.00/0.99  --prolific_symb_bound                   200
% 4.00/0.99  --lt_threshold                          2000
% 4.00/0.99  --clause_weak_htbl                      true
% 4.00/0.99  --gc_record_bc_elim                     false
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing Options
% 4.00/0.99  
% 4.00/0.99  --preprocessing_flag                    true
% 4.00/0.99  --time_out_prep_mult                    0.1
% 4.00/0.99  --splitting_mode                        input
% 4.00/0.99  --splitting_grd                         true
% 4.00/0.99  --splitting_cvd                         false
% 4.00/0.99  --splitting_cvd_svl                     false
% 4.00/0.99  --splitting_nvd                         32
% 4.00/0.99  --sub_typing                            true
% 4.00/0.99  --prep_gs_sim                           true
% 4.00/0.99  --prep_unflatten                        true
% 4.00/0.99  --prep_res_sim                          true
% 4.00/0.99  --prep_upred                            true
% 4.00/0.99  --prep_sem_filter                       exhaustive
% 4.00/0.99  --prep_sem_filter_out                   false
% 4.00/0.99  --pred_elim                             true
% 4.00/0.99  --res_sim_input                         true
% 4.00/0.99  --eq_ax_congr_red                       true
% 4.00/0.99  --pure_diseq_elim                       true
% 4.00/0.99  --brand_transform                       false
% 4.00/0.99  --non_eq_to_eq                          false
% 4.00/0.99  --prep_def_merge                        true
% 4.00/0.99  --prep_def_merge_prop_impl              false
% 4.00/0.99  --prep_def_merge_mbd                    true
% 4.00/0.99  --prep_def_merge_tr_red                 false
% 4.00/0.99  --prep_def_merge_tr_cl                  false
% 4.00/0.99  --smt_preprocessing                     true
% 4.00/0.99  --smt_ac_axioms                         fast
% 4.00/0.99  --preprocessed_out                      false
% 4.00/0.99  --preprocessed_stats                    false
% 4.00/0.99  
% 4.00/0.99  ------ Abstraction refinement Options
% 4.00/0.99  
% 4.00/0.99  --abstr_ref                             []
% 4.00/0.99  --abstr_ref_prep                        false
% 4.00/0.99  --abstr_ref_until_sat                   false
% 4.00/0.99  --abstr_ref_sig_restrict                funpre
% 4.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.99  --abstr_ref_under                       []
% 4.00/0.99  
% 4.00/0.99  ------ SAT Options
% 4.00/0.99  
% 4.00/0.99  --sat_mode                              false
% 4.00/0.99  --sat_fm_restart_options                ""
% 4.00/0.99  --sat_gr_def                            false
% 4.00/0.99  --sat_epr_types                         true
% 4.00/0.99  --sat_non_cyclic_types                  false
% 4.00/0.99  --sat_finite_models                     false
% 4.00/0.99  --sat_fm_lemmas                         false
% 4.00/0.99  --sat_fm_prep                           false
% 4.00/0.99  --sat_fm_uc_incr                        true
% 4.00/0.99  --sat_out_model                         small
% 4.00/0.99  --sat_out_clauses                       false
% 4.00/0.99  
% 4.00/0.99  ------ QBF Options
% 4.00/0.99  
% 4.00/0.99  --qbf_mode                              false
% 4.00/0.99  --qbf_elim_univ                         false
% 4.00/0.99  --qbf_dom_inst                          none
% 4.00/0.99  --qbf_dom_pre_inst                      false
% 4.00/0.99  --qbf_sk_in                             false
% 4.00/0.99  --qbf_pred_elim                         true
% 4.00/0.99  --qbf_split                             512
% 4.00/0.99  
% 4.00/0.99  ------ BMC1 Options
% 4.00/0.99  
% 4.00/0.99  --bmc1_incremental                      false
% 4.00/0.99  --bmc1_axioms                           reachable_all
% 4.00/0.99  --bmc1_min_bound                        0
% 4.00/0.99  --bmc1_max_bound                        -1
% 4.00/0.99  --bmc1_max_bound_default                -1
% 4.00/0.99  --bmc1_symbol_reachability              true
% 4.00/0.99  --bmc1_property_lemmas                  false
% 4.00/0.99  --bmc1_k_induction                      false
% 4.00/0.99  --bmc1_non_equiv_states                 false
% 4.00/0.99  --bmc1_deadlock                         false
% 4.00/0.99  --bmc1_ucm                              false
% 4.00/0.99  --bmc1_add_unsat_core                   none
% 4.00/0.99  --bmc1_unsat_core_children              false
% 4.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.99  --bmc1_out_stat                         full
% 4.00/0.99  --bmc1_ground_init                      false
% 4.00/0.99  --bmc1_pre_inst_next_state              false
% 4.00/0.99  --bmc1_pre_inst_state                   false
% 4.00/0.99  --bmc1_pre_inst_reach_state             false
% 4.00/0.99  --bmc1_out_unsat_core                   false
% 4.00/0.99  --bmc1_aig_witness_out                  false
% 4.00/0.99  --bmc1_verbose                          false
% 4.00/0.99  --bmc1_dump_clauses_tptp                false
% 4.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.99  --bmc1_dump_file                        -
% 4.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.99  --bmc1_ucm_extend_mode                  1
% 4.00/0.99  --bmc1_ucm_init_mode                    2
% 4.00/0.99  --bmc1_ucm_cone_mode                    none
% 4.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.99  --bmc1_ucm_relax_model                  4
% 4.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.99  --bmc1_ucm_layered_model                none
% 4.00/0.99  --bmc1_ucm_max_lemma_size               10
% 4.00/0.99  
% 4.00/0.99  ------ AIG Options
% 4.00/0.99  
% 4.00/0.99  --aig_mode                              false
% 4.00/0.99  
% 4.00/0.99  ------ Instantiation Options
% 4.00/0.99  
% 4.00/0.99  --instantiation_flag                    true
% 4.00/0.99  --inst_sos_flag                         true
% 4.00/0.99  --inst_sos_phase                        true
% 4.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel_side                     num_symb
% 4.00/0.99  --inst_solver_per_active                1400
% 4.00/0.99  --inst_solver_calls_frac                1.
% 4.00/0.99  --inst_passive_queue_type               priority_queues
% 4.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.99  --inst_passive_queues_freq              [25;2]
% 4.00/0.99  --inst_dismatching                      true
% 4.00/0.99  --inst_eager_unprocessed_to_passive     true
% 4.00/0.99  --inst_prop_sim_given                   true
% 4.00/0.99  --inst_prop_sim_new                     false
% 4.00/0.99  --inst_subs_new                         false
% 4.00/0.99  --inst_eq_res_simp                      false
% 4.00/0.99  --inst_subs_given                       false
% 4.00/0.99  --inst_orphan_elimination               true
% 4.00/0.99  --inst_learning_loop_flag               true
% 4.00/0.99  --inst_learning_start                   3000
% 4.00/0.99  --inst_learning_factor                  2
% 4.00/0.99  --inst_start_prop_sim_after_learn       3
% 4.00/0.99  --inst_sel_renew                        solver
% 4.00/0.99  --inst_lit_activity_flag                true
% 4.00/0.99  --inst_restr_to_given                   false
% 4.00/0.99  --inst_activity_threshold               500
% 4.00/0.99  --inst_out_proof                        true
% 4.00/0.99  
% 4.00/0.99  ------ Resolution Options
% 4.00/0.99  
% 4.00/0.99  --resolution_flag                       true
% 4.00/0.99  --res_lit_sel                           adaptive
% 4.00/0.99  --res_lit_sel_side                      none
% 4.00/0.99  --res_ordering                          kbo
% 4.00/0.99  --res_to_prop_solver                    active
% 4.00/0.99  --res_prop_simpl_new                    false
% 4.00/0.99  --res_prop_simpl_given                  true
% 4.00/0.99  --res_passive_queue_type                priority_queues
% 4.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.99  --res_passive_queues_freq               [15;5]
% 4.00/0.99  --res_forward_subs                      full
% 4.00/0.99  --res_backward_subs                     full
% 4.00/0.99  --res_forward_subs_resolution           true
% 4.00/0.99  --res_backward_subs_resolution          true
% 4.00/0.99  --res_orphan_elimination                true
% 4.00/0.99  --res_time_limit                        2.
% 4.00/0.99  --res_out_proof                         true
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Options
% 4.00/0.99  
% 4.00/0.99  --superposition_flag                    true
% 4.00/0.99  --sup_passive_queue_type                priority_queues
% 4.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.99  --demod_completeness_check              fast
% 4.00/0.99  --demod_use_ground                      true
% 4.00/0.99  --sup_to_prop_solver                    passive
% 4.00/0.99  --sup_prop_simpl_new                    true
% 4.00/0.99  --sup_prop_simpl_given                  true
% 4.00/0.99  --sup_fun_splitting                     true
% 4.00/0.99  --sup_smt_interval                      50000
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Simplification Setup
% 4.00/0.99  
% 4.00/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.00/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_immed_triv                        [TrivRules]
% 4.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_bw_main                     []
% 4.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_input_bw                          []
% 4.00/0.99  
% 4.00/0.99  ------ Combination Options
% 4.00/0.99  
% 4.00/0.99  --comb_res_mult                         3
% 4.00/0.99  --comb_sup_mult                         2
% 4.00/0.99  --comb_inst_mult                        10
% 4.00/0.99  
% 4.00/0.99  ------ Debug Options
% 4.00/0.99  
% 4.00/0.99  --dbg_backtrace                         false
% 4.00/0.99  --dbg_dump_prop_clauses                 false
% 4.00/0.99  --dbg_dump_prop_clauses_file            -
% 4.00/0.99  --dbg_out_stat                          false
% 4.00/0.99  ------ Parsing...
% 4.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.99  ------ Proving...
% 4.00/0.99  ------ Problem Properties 
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  clauses                                 24
% 4.00/0.99  conjectures                             1
% 4.00/0.99  EPR                                     4
% 4.00/0.99  Horn                                    14
% 4.00/0.99  unary                                   1
% 4.00/0.99  binary                                  11
% 4.00/0.99  lits                                    64
% 4.00/0.99  lits eq                                 3
% 4.00/0.99  fd_pure                                 0
% 4.00/0.99  fd_pseudo                               0
% 4.00/0.99  fd_cond                                 0
% 4.00/0.99  fd_pseudo_cond                          3
% 4.00/0.99  AC symbols                              0
% 4.00/0.99  
% 4.00/0.99  ------ Schedule dynamic 5 is on 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  ------ 
% 4.00/0.99  Current options:
% 4.00/0.99  ------ 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options
% 4.00/0.99  
% 4.00/0.99  --out_options                           all
% 4.00/0.99  --tptp_safe_out                         true
% 4.00/0.99  --problem_path                          ""
% 4.00/0.99  --include_path                          ""
% 4.00/0.99  --clausifier                            res/vclausify_rel
% 4.00/0.99  --clausifier_options                    ""
% 4.00/0.99  --stdin                                 false
% 4.00/0.99  --stats_out                             all
% 4.00/0.99  
% 4.00/0.99  ------ General Options
% 4.00/0.99  
% 4.00/0.99  --fof                                   false
% 4.00/0.99  --time_out_real                         305.
% 4.00/0.99  --time_out_virtual                      -1.
% 4.00/0.99  --symbol_type_check                     false
% 4.00/0.99  --clausify_out                          false
% 4.00/0.99  --sig_cnt_out                           false
% 4.00/0.99  --trig_cnt_out                          false
% 4.00/0.99  --trig_cnt_out_tolerance                1.
% 4.00/0.99  --trig_cnt_out_sk_spl                   false
% 4.00/0.99  --abstr_cl_out                          false
% 4.00/0.99  
% 4.00/0.99  ------ Global Options
% 4.00/0.99  
% 4.00/0.99  --schedule                              default
% 4.00/0.99  --add_important_lit                     false
% 4.00/0.99  --prop_solver_per_cl                    1000
% 4.00/0.99  --min_unsat_core                        false
% 4.00/0.99  --soft_assumptions                      false
% 4.00/0.99  --soft_lemma_size                       3
% 4.00/0.99  --prop_impl_unit_size                   0
% 4.00/0.99  --prop_impl_unit                        []
% 4.00/0.99  --share_sel_clauses                     true
% 4.00/0.99  --reset_solvers                         false
% 4.00/0.99  --bc_imp_inh                            [conj_cone]
% 4.00/0.99  --conj_cone_tolerance                   3.
% 4.00/0.99  --extra_neg_conj                        none
% 4.00/0.99  --large_theory_mode                     true
% 4.00/0.99  --prolific_symb_bound                   200
% 4.00/0.99  --lt_threshold                          2000
% 4.00/0.99  --clause_weak_htbl                      true
% 4.00/0.99  --gc_record_bc_elim                     false
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing Options
% 4.00/0.99  
% 4.00/0.99  --preprocessing_flag                    true
% 4.00/0.99  --time_out_prep_mult                    0.1
% 4.00/0.99  --splitting_mode                        input
% 4.00/0.99  --splitting_grd                         true
% 4.00/0.99  --splitting_cvd                         false
% 4.00/0.99  --splitting_cvd_svl                     false
% 4.00/0.99  --splitting_nvd                         32
% 4.00/0.99  --sub_typing                            true
% 4.00/0.99  --prep_gs_sim                           true
% 4.00/0.99  --prep_unflatten                        true
% 4.00/0.99  --prep_res_sim                          true
% 4.00/0.99  --prep_upred                            true
% 4.00/0.99  --prep_sem_filter                       exhaustive
% 4.00/0.99  --prep_sem_filter_out                   false
% 4.00/0.99  --pred_elim                             true
% 4.00/0.99  --res_sim_input                         true
% 4.00/0.99  --eq_ax_congr_red                       true
% 4.00/0.99  --pure_diseq_elim                       true
% 4.00/0.99  --brand_transform                       false
% 4.00/0.99  --non_eq_to_eq                          false
% 4.00/0.99  --prep_def_merge                        true
% 4.00/0.99  --prep_def_merge_prop_impl              false
% 4.00/0.99  --prep_def_merge_mbd                    true
% 4.00/0.99  --prep_def_merge_tr_red                 false
% 4.00/0.99  --prep_def_merge_tr_cl                  false
% 4.00/0.99  --smt_preprocessing                     true
% 4.00/0.99  --smt_ac_axioms                         fast
% 4.00/0.99  --preprocessed_out                      false
% 4.00/0.99  --preprocessed_stats                    false
% 4.00/0.99  
% 4.00/0.99  ------ Abstraction refinement Options
% 4.00/0.99  
% 4.00/0.99  --abstr_ref                             []
% 4.00/0.99  --abstr_ref_prep                        false
% 4.00/0.99  --abstr_ref_until_sat                   false
% 4.00/0.99  --abstr_ref_sig_restrict                funpre
% 4.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.99  --abstr_ref_under                       []
% 4.00/0.99  
% 4.00/0.99  ------ SAT Options
% 4.00/0.99  
% 4.00/0.99  --sat_mode                              false
% 4.00/0.99  --sat_fm_restart_options                ""
% 4.00/0.99  --sat_gr_def                            false
% 4.00/0.99  --sat_epr_types                         true
% 4.00/0.99  --sat_non_cyclic_types                  false
% 4.00/0.99  --sat_finite_models                     false
% 4.00/0.99  --sat_fm_lemmas                         false
% 4.00/0.99  --sat_fm_prep                           false
% 4.00/0.99  --sat_fm_uc_incr                        true
% 4.00/0.99  --sat_out_model                         small
% 4.00/0.99  --sat_out_clauses                       false
% 4.00/0.99  
% 4.00/0.99  ------ QBF Options
% 4.00/0.99  
% 4.00/0.99  --qbf_mode                              false
% 4.00/0.99  --qbf_elim_univ                         false
% 4.00/0.99  --qbf_dom_inst                          none
% 4.00/0.99  --qbf_dom_pre_inst                      false
% 4.00/0.99  --qbf_sk_in                             false
% 4.00/0.99  --qbf_pred_elim                         true
% 4.00/0.99  --qbf_split                             512
% 4.00/0.99  
% 4.00/0.99  ------ BMC1 Options
% 4.00/0.99  
% 4.00/0.99  --bmc1_incremental                      false
% 4.00/0.99  --bmc1_axioms                           reachable_all
% 4.00/0.99  --bmc1_min_bound                        0
% 4.00/0.99  --bmc1_max_bound                        -1
% 4.00/0.99  --bmc1_max_bound_default                -1
% 4.00/0.99  --bmc1_symbol_reachability              true
% 4.00/0.99  --bmc1_property_lemmas                  false
% 4.00/0.99  --bmc1_k_induction                      false
% 4.00/0.99  --bmc1_non_equiv_states                 false
% 4.00/0.99  --bmc1_deadlock                         false
% 4.00/0.99  --bmc1_ucm                              false
% 4.00/0.99  --bmc1_add_unsat_core                   none
% 4.00/0.99  --bmc1_unsat_core_children              false
% 4.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.99  --bmc1_out_stat                         full
% 4.00/0.99  --bmc1_ground_init                      false
% 4.00/0.99  --bmc1_pre_inst_next_state              false
% 4.00/0.99  --bmc1_pre_inst_state                   false
% 4.00/0.99  --bmc1_pre_inst_reach_state             false
% 4.00/0.99  --bmc1_out_unsat_core                   false
% 4.00/0.99  --bmc1_aig_witness_out                  false
% 4.00/0.99  --bmc1_verbose                          false
% 4.00/0.99  --bmc1_dump_clauses_tptp                false
% 4.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.99  --bmc1_dump_file                        -
% 4.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.99  --bmc1_ucm_extend_mode                  1
% 4.00/0.99  --bmc1_ucm_init_mode                    2
% 4.00/0.99  --bmc1_ucm_cone_mode                    none
% 4.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.99  --bmc1_ucm_relax_model                  4
% 4.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.99  --bmc1_ucm_layered_model                none
% 4.00/0.99  --bmc1_ucm_max_lemma_size               10
% 4.00/0.99  
% 4.00/0.99  ------ AIG Options
% 4.00/0.99  
% 4.00/0.99  --aig_mode                              false
% 4.00/0.99  
% 4.00/0.99  ------ Instantiation Options
% 4.00/0.99  
% 4.00/0.99  --instantiation_flag                    true
% 4.00/0.99  --inst_sos_flag                         true
% 4.00/0.99  --inst_sos_phase                        true
% 4.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel_side                     none
% 4.00/0.99  --inst_solver_per_active                1400
% 4.00/0.99  --inst_solver_calls_frac                1.
% 4.00/0.99  --inst_passive_queue_type               priority_queues
% 4.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.99  --inst_passive_queues_freq              [25;2]
% 4.00/0.99  --inst_dismatching                      true
% 4.00/0.99  --inst_eager_unprocessed_to_passive     true
% 4.00/0.99  --inst_prop_sim_given                   true
% 4.00/0.99  --inst_prop_sim_new                     false
% 4.00/0.99  --inst_subs_new                         false
% 4.00/0.99  --inst_eq_res_simp                      false
% 4.00/0.99  --inst_subs_given                       false
% 4.00/0.99  --inst_orphan_elimination               true
% 4.00/0.99  --inst_learning_loop_flag               true
% 4.00/0.99  --inst_learning_start                   3000
% 4.00/0.99  --inst_learning_factor                  2
% 4.00/0.99  --inst_start_prop_sim_after_learn       3
% 4.00/0.99  --inst_sel_renew                        solver
% 4.00/0.99  --inst_lit_activity_flag                true
% 4.00/0.99  --inst_restr_to_given                   false
% 4.00/0.99  --inst_activity_threshold               500
% 4.00/0.99  --inst_out_proof                        true
% 4.00/0.99  
% 4.00/0.99  ------ Resolution Options
% 4.00/0.99  
% 4.00/0.99  --resolution_flag                       false
% 4.00/0.99  --res_lit_sel                           adaptive
% 4.00/0.99  --res_lit_sel_side                      none
% 4.00/0.99  --res_ordering                          kbo
% 4.00/0.99  --res_to_prop_solver                    active
% 4.00/0.99  --res_prop_simpl_new                    false
% 4.00/0.99  --res_prop_simpl_given                  true
% 4.00/0.99  --res_passive_queue_type                priority_queues
% 4.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.99  --res_passive_queues_freq               [15;5]
% 4.00/0.99  --res_forward_subs                      full
% 4.00/0.99  --res_backward_subs                     full
% 4.00/0.99  --res_forward_subs_resolution           true
% 4.00/0.99  --res_backward_subs_resolution          true
% 4.00/0.99  --res_orphan_elimination                true
% 4.00/0.99  --res_time_limit                        2.
% 4.00/0.99  --res_out_proof                         true
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Options
% 4.00/0.99  
% 4.00/0.99  --superposition_flag                    true
% 4.00/0.99  --sup_passive_queue_type                priority_queues
% 4.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.99  --demod_completeness_check              fast
% 4.00/0.99  --demod_use_ground                      true
% 4.00/0.99  --sup_to_prop_solver                    passive
% 4.00/0.99  --sup_prop_simpl_new                    true
% 4.00/0.99  --sup_prop_simpl_given                  true
% 4.00/0.99  --sup_fun_splitting                     true
% 4.00/0.99  --sup_smt_interval                      50000
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Simplification Setup
% 4.00/0.99  
% 4.00/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.00/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_immed_triv                        [TrivRules]
% 4.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_bw_main                     []
% 4.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_input_bw                          []
% 4.00/0.99  
% 4.00/0.99  ------ Combination Options
% 4.00/0.99  
% 4.00/0.99  --comb_res_mult                         3
% 4.00/0.99  --comb_sup_mult                         2
% 4.00/0.99  --comb_inst_mult                        10
% 4.00/0.99  
% 4.00/0.99  ------ Debug Options
% 4.00/0.99  
% 4.00/0.99  --dbg_backtrace                         false
% 4.00/0.99  --dbg_dump_prop_clauses                 false
% 4.00/0.99  --dbg_dump_prop_clauses_file            -
% 4.00/0.99  --dbg_out_stat                          false
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  ------ Proving...
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  % SZS status Theorem for theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  fof(f2,axiom,(
% 4.00/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f6,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(ennf_transformation,[],[f2])).
% 4.00/0.99  
% 4.00/0.99  fof(f7,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(flattening,[],[f6])).
% 4.00/0.99  
% 4.00/0.99  fof(f19,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(nnf_transformation,[],[f7])).
% 4.00/0.99  
% 4.00/0.99  fof(f20,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(rectify,[],[f19])).
% 4.00/0.99  
% 4.00/0.99  fof(f21,plain,(
% 4.00/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f22,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 4.00/0.99  
% 4.00/0.99  fof(f38,plain,(
% 4.00/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f22])).
% 4.00/0.99  
% 4.00/0.99  fof(f4,conjecture,(
% 4.00/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) => r2_lattice3(X0,k2_xboole_0(X1,X2),X3)) & ((r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) => r1_lattice3(X0,k2_xboole_0(X1,X2),X3)))))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f5,negated_conjecture,(
% 4.00/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1,X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) => r2_lattice3(X0,k2_xboole_0(X1,X2),X3)) & ((r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) => r1_lattice3(X0,k2_xboole_0(X1,X2),X3)))))),
% 4.00/0.99    inference(negated_conjecture,[],[f4])).
% 4.00/0.99  
% 4.00/0.99  fof(f10,plain,(
% 4.00/0.99    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & (r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3))) | (~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & (r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)))) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0))),
% 4.00/0.99    inference(ennf_transformation,[],[f5])).
% 4.00/0.99  
% 4.00/0.99  fof(f11,plain,(
% 4.00/0.99    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | (~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0))),
% 4.00/0.99    inference(flattening,[],[f10])).
% 4.00/0.99  
% 4.00/0.99  fof(f12,plain,(
% 4.00/0.99    ! [X3,X2,X1,X0] : ((~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 4.00/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.00/0.99  
% 4.00/0.99  fof(f13,plain,(
% 4.00/0.99    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | sP0(X3,X2,X1,X0)) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0))),
% 4.00/0.99    inference(definition_folding,[],[f11,f12])).
% 4.00/0.99  
% 4.00/0.99  fof(f30,plain,(
% 4.00/0.99    ( ! [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | sP0(X3,X2,X1,X0)) & m1_subset_1(X3,u1_struct_0(X0))) => (((~r2_lattice3(X0,k2_xboole_0(sK5,sK6),sK7) & r2_lattice3(X0,sK6,sK7) & r2_lattice3(X0,sK5,sK7)) | sP0(sK7,sK6,sK5,X0)) & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f29,plain,(
% 4.00/0.99    ? [X0] : (? [X1,X2,X3] : (((~r2_lattice3(X0,k2_xboole_0(X1,X2),X3) & r2_lattice3(X0,X2,X3) & r2_lattice3(X0,X1,X3)) | sP0(X3,X2,X1,X0)) & m1_subset_1(X3,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X3,X2,X1] : (((~r2_lattice3(sK4,k2_xboole_0(X1,X2),X3) & r2_lattice3(sK4,X2,X3) & r2_lattice3(sK4,X1,X3)) | sP0(X3,X2,X1,sK4)) & m1_subset_1(X3,u1_struct_0(sK4))) & l1_orders_2(sK4))),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f31,plain,(
% 4.00/0.99    (((~r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) & r2_lattice3(sK4,sK6,sK7) & r2_lattice3(sK4,sK5,sK7)) | sP0(sK7,sK6,sK5,sK4)) & m1_subset_1(sK7,u1_struct_0(sK4))) & l1_orders_2(sK4)),
% 4.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f13,f30,f29])).
% 4.00/0.99  
% 4.00/0.99  fof(f49,plain,(
% 4.00/0.99    l1_orders_2(sK4)),
% 4.00/0.99    inference(cnf_transformation,[],[f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f40,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f22])).
% 4.00/0.99  
% 4.00/0.99  fof(f1,axiom,(
% 4.00/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f14,plain,(
% 4.00/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.00/0.99    inference(nnf_transformation,[],[f1])).
% 4.00/0.99  
% 4.00/0.99  fof(f15,plain,(
% 4.00/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.00/0.99    inference(flattening,[],[f14])).
% 4.00/0.99  
% 4.00/0.99  fof(f16,plain,(
% 4.00/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.00/0.99    inference(rectify,[],[f15])).
% 4.00/0.99  
% 4.00/0.99  fof(f17,plain,(
% 4.00/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f18,plain,(
% 4.00/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 4.00/0.99  
% 4.00/0.99  fof(f32,plain,(
% 4.00/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.00/0.99    inference(cnf_transformation,[],[f18])).
% 4.00/0.99  
% 4.00/0.99  fof(f56,plain,(
% 4.00/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 4.00/0.99    inference(equality_resolution,[],[f32])).
% 4.00/0.99  
% 4.00/0.99  fof(f39,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f22])).
% 4.00/0.99  
% 4.00/0.99  fof(f41,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f22])).
% 4.00/0.99  
% 4.00/0.99  fof(f27,plain,(
% 4.00/0.99    ! [X3,X2,X1,X0] : ((~r1_lattice3(X0,k2_xboole_0(X1,X2),X3) & r1_lattice3(X0,X2,X3) & r1_lattice3(X0,X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 4.00/0.99    inference(nnf_transformation,[],[f12])).
% 4.00/0.99  
% 4.00/0.99  fof(f28,plain,(
% 4.00/0.99    ! [X0,X1,X2,X3] : ((~r1_lattice3(X3,k2_xboole_0(X2,X1),X0) & r1_lattice3(X3,X1,X0) & r1_lattice3(X3,X2,X0)) | ~sP0(X0,X1,X2,X3))),
% 4.00/0.99    inference(rectify,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  fof(f48,plain,(
% 4.00/0.99    ( ! [X2,X0,X3,X1] : (~r1_lattice3(X3,k2_xboole_0(X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f28])).
% 4.00/0.99  
% 4.00/0.99  fof(f52,plain,(
% 4.00/0.99    r2_lattice3(sK4,sK6,sK7) | sP0(sK7,sK6,sK5,sK4)),
% 4.00/0.99    inference(cnf_transformation,[],[f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f51,plain,(
% 4.00/0.99    r2_lattice3(sK4,sK5,sK7) | sP0(sK7,sK6,sK5,sK4)),
% 4.00/0.99    inference(cnf_transformation,[],[f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f3,axiom,(
% 4.00/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f8,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(ennf_transformation,[],[f3])).
% 4.00/0.99  
% 4.00/0.99  fof(f9,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(flattening,[],[f8])).
% 4.00/0.99  
% 4.00/0.99  fof(f23,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(nnf_transformation,[],[f9])).
% 4.00/0.99  
% 4.00/0.99  fof(f24,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(rectify,[],[f23])).
% 4.00/0.99  
% 4.00/0.99  fof(f25,plain,(
% 4.00/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f26,plain,(
% 4.00/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 4.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 4.00/0.99  
% 4.00/0.99  fof(f44,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f26])).
% 4.00/0.99  
% 4.00/0.99  fof(f43,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f26])).
% 4.00/0.99  
% 4.00/0.99  fof(f46,plain,(
% 4.00/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X3,X2,X0) | ~sP0(X0,X1,X2,X3)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f28])).
% 4.00/0.99  
% 4.00/0.99  fof(f42,plain,(
% 4.00/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f26])).
% 4.00/0.99  
% 4.00/0.99  fof(f50,plain,(
% 4.00/0.99    m1_subset_1(sK7,u1_struct_0(sK4))),
% 4.00/0.99    inference(cnf_transformation,[],[f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f45,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f26])).
% 4.00/0.99  
% 4.00/0.99  fof(f53,plain,(
% 4.00/0.99    ~r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) | sP0(sK7,sK6,sK5,sK4)),
% 4.00/0.99    inference(cnf_transformation,[],[f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f47,plain,(
% 4.00/0.99    ( ! [X2,X0,X3,X1] : (r1_lattice3(X3,X1,X0) | ~sP0(X0,X1,X2,X3)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f28])).
% 4.00/0.99  
% 4.00/0.99  cnf(c_9,plain,
% 4.00/0.99      ( r1_orders_2(X0,X1,X2)
% 4.00/0.99      | ~ r1_lattice3(X0,X3,X1)
% 4.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/0.99      | ~ r2_hidden(X2,X3)
% 4.00/0.99      | ~ l1_orders_2(X0) ),
% 4.00/0.99      inference(cnf_transformation,[],[f38]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_21,negated_conjecture,
% 4.00/0.99      ( l1_orders_2(sK4) ),
% 4.00/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_429,plain,
% 4.00/0.99      ( r1_orders_2(X0,X1,X2)
% 4.00/0.99      | ~ r1_lattice3(X0,X3,X1)
% 4.00/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.00/0.99      | ~ r2_hidden(X2,X3)
% 4.00/0.99      | sK4 != X0 ),
% 4.00/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_430,plain,
% 4.00/0.99      ( r1_orders_2(sK4,X0,X1)
% 4.00/0.99      | ~ r1_lattice3(sK4,X2,X0)
% 4.00/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/0.99      | ~ r2_hidden(X1,X2) ),
% 4.00/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3694,plain,
% 4.00/0.99      ( r1_orders_2(sK4,X0,sK2(X1,k2_xboole_0(sK5,sK6),sK7))
% 4.00/0.99      | ~ r1_lattice3(sK4,X2,X0)
% 4.00/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/0.99      | ~ m1_subset_1(sK2(X1,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/0.99      | ~ r2_hidden(sK2(X1,k2_xboole_0(sK5,sK6),sK7),X2) ),
% 4.00/0.99      inference(instantiation,[status(thm)],[c_430]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4071,plain,
% 4.00/0.99      ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
% 4.00/0.99      | ~ r1_lattice3(sK4,X1,sK7)
% 4.00/0.99      | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/0.99      | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),X1) ),
% 4.00/0.99      inference(instantiation,[status(thm)],[c_3694]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8610,plain,
% 4.00/0.99      ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
% 4.00/0.99      | ~ r1_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK6) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_4071]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8611,plain,
% 4.00/1.00      ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_8610]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8613,plain,
% 4.00/1.00      ( r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_8611]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8605,plain,
% 4.00/1.00      ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7))
% 4.00/1.00      | ~ r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK5) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_4071]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8606,plain,
% 4.00/1.00      ( r1_orders_2(sK4,sK7,sK2(X0,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(X0,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(X0,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_8605]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8608,plain,
% 4.00/1.00      ( r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_8606]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_7,plain,
% 4.00/1.00      ( r1_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_465,plain,
% 4.00/1.00      ( r1_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_466,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK2(sK4,X0,X1),X0) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2217,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5,plain,
% 4.00/1.00      ( r2_hidden(X0,X1)
% 4.00/1.00      | r2_hidden(X0,X2)
% 4.00/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 4.00/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2234,plain,
% 4.00/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.00/1.00      | r2_hidden(X0,X2) = iProver_top
% 4.00/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2712,plain,
% 4.00/1.00      ( r1_lattice3(sK4,k2_xboole_0(X0,X1),X2) = iProver_top
% 4.00/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2217,c_2234]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_8,plain,
% 4.00/1.00      ( r1_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_450,plain,
% 4.00/1.00      ( r1_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_451,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_450]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2218,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2219,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X2,X0) != iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X1,X2) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3022,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK2(sK4,X1,X2)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X3,X0) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X1,X2) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,X1,X2),X3) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2218,c_2219]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4050,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK2(sK4,k2_xboole_0(X1,X2),X3)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X2,X0) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(X1,X2),X3) = iProver_top
% 4.00/1.00      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(X1,X2),X3),X1) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2712,c_3022]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_6,plain,
% 4.00/1.00      ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
% 4.00/1.00      | r1_lattice3(X0,X2,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_480,plain,
% 4.00/1.00      ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
% 4.00/1.00      | r1_lattice3(X0,X2,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_481,plain,
% 4.00/1.00      ( ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
% 4.00/1.00      | r1_lattice3(sK4,X1,X0)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2216,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK2(sK4,X1,X0)) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X1,X0) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_6712,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(X2,X0),X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(X2,X0),X1),X2) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_4050,c_2216]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_6817,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK2(sK4,k2_xboole_0(X1,X2),X3)) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X2,X3) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X1,X0) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(X1,X2),X3) = iProver_top
% 4.00/1.00      | m1_subset_1(X3,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_6712,c_3022]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_7004,plain,
% 4.00/1.00      ( r1_lattice3(sK4,X0,X1) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,X2,X1) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(X2,X0),X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_6817,c_2216]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_14,plain,
% 4.00/1.00      ( ~ sP0(X0,X1,X2,X3) | ~ r1_lattice3(X3,k2_xboole_0(X2,X1),X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f48]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_18,negated_conjecture,
% 4.00/1.00      ( sP0(sK7,sK6,sK5,sK4) | r2_lattice3(sK4,sK6,sK7) ),
% 4.00/1.00      inference(cnf_transformation,[],[f52]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_316,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
% 4.00/1.00      | sK7 != X3
% 4.00/1.00      | sK6 != X2
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_317,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_316]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2225,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_7850,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_7004,c_2225]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_19,negated_conjecture,
% 4.00/1.00      ( sP0(sK7,sK6,sK5,sK4) | r2_lattice3(sK4,sK5,sK7) ),
% 4.00/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_306,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
% 4.00/1.00      | sK7 != X3
% 4.00/1.00      | sK6 != X2
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_307,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_306]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2226,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_7849,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_7004,c_2226]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4633,plain,
% 4.00/1.00      ( r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0)
% 4.00/1.00      | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(X0,sK6))
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_6129,plain,
% 4.00/1.00      ( ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6))
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6)
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_4633]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_6130,plain,
% 4.00/1.00      ( r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_6129]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_11,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | r2_hidden(sK3(X0,X1,X2),X1)
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f44]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_399,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | r2_hidden(sK3(X0,X1,X2),X1)
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_400,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),X0) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2221,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3310,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(X0,X1),X2) = iProver_top
% 4.00/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2221,c_2234]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_12,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f43]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_384,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_385,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_384]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2222,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_16,plain,
% 4.00/1.00      ( ~ sP0(X0,X1,X2,X3) | r1_lattice3(X3,X2,X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f46]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_256,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X3
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_257,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) | r1_lattice3(sK4,sK5,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_256]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2231,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_13,plain,
% 4.00/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 4.00/1.00      | r1_orders_2(X0,X3,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 4.00/1.00      | ~ r2_hidden(X3,X1)
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_363,plain,
% 4.00/1.00      ( ~ r2_lattice3(X0,X1,X2)
% 4.00/1.00      | r1_orders_2(X0,X3,X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 4.00/1.00      | ~ r2_hidden(X3,X1)
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_364,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,X0,X1)
% 4.00/1.00      | r1_orders_2(sK4,X2,X1)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X2,X0) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_363]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2223,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) != iProver_top
% 4.00/1.00      | r1_orders_2(sK4,X2,X1) = iProver_top
% 4.00/1.00      | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2929,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2231,c_2223]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1604,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,X1)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,X2)
% 4.00/1.00      | sK7 != X1
% 4.00/1.00      | sK6 != X2
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_257,c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1605,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK6) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_1604]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_20,negated_conjecture,
% 4.00/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1609,plain,
% 4.00/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | ~ r2_hidden(X0,sK6) ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_1605,c_20]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1610,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK6) ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_1609]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1611,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1610]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3486,plain,
% 4.00/1.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_2929,c_1611]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3487,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_3486]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3491,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2222,c_3487]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_10,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | ~ l1_orders_2(X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_414,plain,
% 4.00/1.00      ( r2_lattice3(X0,X1,X2)
% 4.00/1.00      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
% 4.00/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_415,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1)
% 4.00/1.00      | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2220,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4322,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3491,c_2220]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_23,plain,
% 4.00/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4327,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_4322,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4328,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_4327]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4334,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3310,c_4328]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5637,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_4334,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5638,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_5637]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5645,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK6,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_5638,c_4328]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_17,negated_conjecture,
% 4.00/1.00      ( sP0(sK7,sK6,sK5,sK4)
% 4.00/1.00      | ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
% 4.00/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_266,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X3
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_17]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_267,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_266]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_268,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_246,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X3
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_247,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) | r1_lattice3(sK4,sK5,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_246]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2232,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3019,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2232,c_2223]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1676,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,X1)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,X2)
% 4.00/1.00      | sK7 != X1
% 4.00/1.00      | sK5 != X2
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_247,c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1677,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK5) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_1676]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1681,plain,
% 4.00/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | ~ r2_hidden(X0,sK5) ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_1677,c_20]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1682,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK5) ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_1681]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1683,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3755,plain,
% 4.00/1.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_3019,c_1683]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3756,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_3755]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3760,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2222,c_3756]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4629,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3760,c_2220]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4683,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_4629,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4684,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_4683]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5646,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_5638,c_4684]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5656,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK5,sK7) = iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_5645,c_268,c_5646]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_15,plain,
% 4.00/1.00      ( ~ sP0(X0,X1,X2,X3) | r1_lattice3(X3,X1,X0) ),
% 4.00/1.00      inference(cnf_transformation,[],[f47]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_286,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X1
% 4.00/1.00      | sK5 != X3
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_287,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) | r1_lattice3(sK4,sK6,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2228,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2886,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2228,c_2223]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1580,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,X1)
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,X2)
% 4.00/1.00      | sK7 != X1
% 4.00/1.00      | sK6 != X2
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_287,c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1581,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK6) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_1580]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1582,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1581]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3361,plain,
% 4.00/1.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_2886,c_23,c_1582]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3362,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_3361]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3366,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2222,c_3362]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3952,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3366,c_2220]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3957,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_3952,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3958,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_3957]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3964,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3310,c_3958]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5178,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_3964,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5179,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(X0,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(X0,sK6),sK7),X0) = iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_5178]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5187,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK6,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_5179,c_3958]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_296,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X1
% 4.00/1.00      | sK5 != X3
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_297,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_296]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_298,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_276,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | r1_lattice3(X0,X1,X2)
% 4.00/1.00      | sK7 != X2
% 4.00/1.00      | sK6 != X1
% 4.00/1.00      | sK5 != X3
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_277,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) | r1_lattice3(sK4,sK6,sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_276]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2229,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2926,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2229,c_2223]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1652,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,X1)
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,X2)
% 4.00/1.00      | sK7 != X1
% 4.00/1.00      | sK5 != X2
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_277,c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1653,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7)
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(X0,sK5) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_1652]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1654,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1653]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3422,plain,
% 4.00/1.00      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_2926,c_23,c_1654]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3423,plain,
% 4.00/1.00      ( r1_orders_2(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_3422]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3427,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,X1) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,X0,X1),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_2222,c_3423]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3995,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_3427,c_2220]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4031,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_3995,c_23]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4032,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(renaming,[status(thm)],[c_4031]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5189,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(superposition,[status(thm)],[c_5179,c_4032]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_5199,plain,
% 4.00/1.00      ( r1_lattice3(sK4,sK6,sK7) = iProver_top ),
% 4.00/1.00      inference(global_propositional_subsumption,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_5187,c_298,c_5189]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2651,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,X0,X1)
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X1)
% 4.00/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2933,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,X0,sK7)
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),X0) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2651]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4111,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,sK5,sK7)
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2933]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4112,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK5,sK7) != iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_4111]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4108,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,sK6,sK7)
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | ~ r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2933]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_4109,plain,
% 4.00/1.00      ( r2_lattice3(sK4,sK6,sK7) != iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_4108]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3293,plain,
% 4.00/1.00      ( r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),X0)
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),X1)
% 4.00/1.00      | ~ r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(X1,X0)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3980,plain,
% 4.00/1.00      ( ~ r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6))
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6)
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_3293]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_3981,plain,
% 4.00/1.00      ( r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK6) = iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),sK5) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_3980]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2305,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7)
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK3(sK4,X0,sK7),X0) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_400]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2349,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2305]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2350,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2349]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2311,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7)
% 4.00/1.00      | ~ r1_orders_2(sK4,sK3(sK4,X0,sK7),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_415]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2346,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2311]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2347,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK3(sK4,k2_xboole_0(sK5,sK6),sK7),sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2346]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2289,plain,
% 4.00/1.00      ( r2_lattice3(sK4,X0,sK7)
% 4.00/1.00      | m1_subset_1(sK3(sK4,X0,sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_385]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2341,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(instantiation,[status(thm)],[c_2289]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_2342,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) = iProver_top
% 4.00/1.00      | m1_subset_1(sK3(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_2341]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_326,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
% 4.00/1.00      | sK7 != X3
% 4.00/1.00      | sK6 != X2
% 4.00/1.00      | sK5 != X1
% 4.00/1.00      | sK4 != X0 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_327,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ r1_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_326]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1022,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | k2_xboole_0(sK5,sK6) != X1
% 4.00/1.00      | sK7 != X0
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_327,c_481]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1023,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_1022]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_1024,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
% 4.00/1.00      | r1_orders_2(sK4,sK7,sK2(sK4,k2_xboole_0(sK5,sK6),sK7)) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_952,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | m1_subset_1(sK2(sK4,X1,X0),u1_struct_0(sK4))
% 4.00/1.00      | k2_xboole_0(sK5,sK6) != X1
% 4.00/1.00      | sK7 != X0
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_327,c_451]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_953,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4))
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_952]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_954,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),u1_struct_0(sK4)) = iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_938,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK2(sK4,X1,X0),X1)
% 4.00/1.00      | k2_xboole_0(sK5,sK6) != X1
% 4.00/1.00      | sK7 != X0
% 4.00/1.00      | sK4 != sK4 ),
% 4.00/1.00      inference(resolution_lifted,[status(thm)],[c_327,c_466]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_939,plain,
% 4.00/1.00      ( ~ r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7)
% 4.00/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) ),
% 4.00/1.00      inference(unflattening,[status(thm)],[c_938]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(c_940,plain,
% 4.00/1.00      ( r2_lattice3(sK4,k2_xboole_0(sK5,sK6),sK7) != iProver_top
% 4.00/1.00      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 4.00/1.00      | r2_hidden(sK2(sK4,k2_xboole_0(sK5,sK6),sK7),k2_xboole_0(sK5,sK6)) = iProver_top ),
% 4.00/1.00      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 4.00/1.00  
% 4.00/1.00  cnf(contradiction,plain,
% 4.00/1.00      ( $false ),
% 4.00/1.00      inference(minisat,
% 4.00/1.00                [status(thm)],
% 4.00/1.00                [c_8613,c_8608,c_7850,c_7849,c_6130,c_5656,c_5199,c_4112,
% 4.00/1.00                 c_4109,c_3981,c_2350,c_2347,c_2342,c_1024,c_954,c_940,
% 4.00/1.00                 c_23]) ).
% 4.00/1.00  
% 4.00/1.00  
% 4.00/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/1.00  
% 4.00/1.00  ------                               Statistics
% 4.00/1.00  
% 4.00/1.00  ------ General
% 4.00/1.00  
% 4.00/1.00  abstr_ref_over_cycles:                  0
% 4.00/1.00  abstr_ref_under_cycles:                 0
% 4.00/1.00  gc_basic_clause_elim:                   0
% 4.00/1.00  forced_gc_time:                         0
% 4.00/1.00  parsing_time:                           0.009
% 4.00/1.00  unif_index_cands_time:                  0.
% 4.00/1.00  unif_index_add_time:                    0.
% 4.00/1.00  orderings_time:                         0.
% 4.00/1.00  out_proof_time:                         0.014
% 4.00/1.00  total_time:                             0.311
% 4.00/1.00  num_of_symbols:                         47
% 4.00/1.00  num_of_terms:                           14343
% 4.00/1.00  
% 4.00/1.00  ------ Preprocessing
% 4.00/1.00  
% 4.00/1.00  num_of_splits:                          0
% 4.00/1.00  num_of_split_atoms:                     0
% 4.00/1.00  num_of_reused_defs:                     0
% 4.00/1.00  num_eq_ax_congr_red:                    19
% 4.00/1.00  num_of_sem_filtered_clauses:            1
% 4.00/1.00  num_of_subtypes:                        0
% 4.00/1.00  monotx_restored_types:                  0
% 4.00/1.00  sat_num_of_epr_types:                   0
% 4.00/1.00  sat_num_of_non_cyclic_types:            0
% 4.00/1.00  sat_guarded_non_collapsed_types:        0
% 4.00/1.00  num_pure_diseq_elim:                    0
% 4.00/1.00  simp_replaced_by:                       0
% 4.00/1.00  res_preprocessed:                       93
% 4.00/1.00  prep_upred:                             0
% 4.00/1.00  prep_unflattend:                        118
% 4.00/1.00  smt_new_axioms:                         0
% 4.00/1.00  pred_elim_cands:                        7
% 4.00/1.00  pred_elim:                              2
% 4.00/1.00  pred_elim_cl:                           -2
% 4.00/1.00  pred_elim_cycles:                       5
% 4.00/1.00  merged_defs:                            0
% 4.00/1.00  merged_defs_ncl:                        0
% 4.00/1.00  bin_hyper_res:                          0
% 4.00/1.00  prep_cycles:                            3
% 4.00/1.00  pred_elim_time:                         0.026
% 4.00/1.00  splitting_time:                         0.
% 4.00/1.00  sem_filter_time:                        0.
% 4.00/1.00  monotx_time:                            0.
% 4.00/1.00  subtype_inf_time:                       0.
% 4.00/1.00  
% 4.00/1.00  ------ Problem properties
% 4.00/1.00  
% 4.00/1.00  clauses:                                24
% 4.00/1.00  conjectures:                            1
% 4.00/1.00  epr:                                    4
% 4.00/1.00  horn:                                   14
% 4.00/1.00  ground:                                 10
% 4.00/1.00  unary:                                  1
% 4.00/1.00  binary:                                 11
% 4.00/1.00  lits:                                   64
% 4.00/1.00  lits_eq:                                3
% 4.00/1.00  fd_pure:                                0
% 4.00/1.00  fd_pseudo:                              0
% 4.00/1.00  fd_cond:                                0
% 4.00/1.00  fd_pseudo_cond:                         3
% 4.00/1.00  ac_symbols:                             0
% 4.00/1.00  
% 4.00/1.00  ------ Propositional Solver
% 4.00/1.00  
% 4.00/1.00  prop_solver_calls:                      27
% 4.00/1.00  prop_fast_solver_calls:                 1647
% 4.00/1.00  smt_solver_calls:                       0
% 4.00/1.00  smt_fast_solver_calls:                  0
% 4.00/1.00  prop_num_of_clauses:                    3576
% 4.00/1.00  prop_preprocess_simplified:             7220
% 4.00/1.00  prop_fo_subsumed:                       110
% 4.00/1.00  prop_solver_time:                       0.
% 4.00/1.00  smt_solver_time:                        0.
% 4.00/1.00  smt_fast_solver_time:                   0.
% 4.00/1.00  prop_fast_solver_time:                  0.
% 4.00/1.00  prop_unsat_core_time:                   0.
% 4.00/1.00  
% 4.00/1.00  ------ QBF
% 4.00/1.00  
% 4.00/1.00  qbf_q_res:                              0
% 4.00/1.00  qbf_num_tautologies:                    0
% 4.00/1.00  qbf_prep_cycles:                        0
% 4.00/1.00  
% 4.00/1.00  ------ BMC1
% 4.00/1.00  
% 4.00/1.00  bmc1_current_bound:                     -1
% 4.00/1.00  bmc1_last_solved_bound:                 -1
% 4.00/1.00  bmc1_unsat_core_size:                   -1
% 4.00/1.00  bmc1_unsat_core_parents_size:           -1
% 4.00/1.00  bmc1_merge_next_fun:                    0
% 4.00/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.00/1.00  
% 4.00/1.00  ------ Instantiation
% 4.00/1.00  
% 4.00/1.00  inst_num_of_clauses:                    682
% 4.00/1.00  inst_num_in_passive:                    309
% 4.00/1.00  inst_num_in_active:                     356
% 4.00/1.00  inst_num_in_unprocessed:                16
% 4.00/1.00  inst_num_of_loops:                      591
% 4.00/1.00  inst_num_of_learning_restarts:          0
% 4.00/1.00  inst_num_moves_active_passive:          228
% 4.00/1.00  inst_lit_activity:                      0
% 4.00/1.00  inst_lit_activity_moves:                0
% 4.00/1.00  inst_num_tautologies:                   0
% 4.00/1.00  inst_num_prop_implied:                  0
% 4.00/1.00  inst_num_existing_simplified:           0
% 4.00/1.00  inst_num_eq_res_simplified:             0
% 4.00/1.00  inst_num_child_elim:                    0
% 4.00/1.00  inst_num_of_dismatching_blockings:      304
% 4.00/1.00  inst_num_of_non_proper_insts:           892
% 4.00/1.00  inst_num_of_duplicates:                 0
% 4.00/1.00  inst_inst_num_from_inst_to_res:         0
% 4.00/1.00  inst_dismatching_checking_time:         0.
% 4.00/1.00  
% 4.00/1.00  ------ Resolution
% 4.00/1.00  
% 4.00/1.00  res_num_of_clauses:                     0
% 4.00/1.00  res_num_in_passive:                     0
% 4.00/1.00  res_num_in_active:                      0
% 4.00/1.00  res_num_of_loops:                       96
% 4.00/1.00  res_forward_subset_subsumed:            72
% 4.00/1.00  res_backward_subset_subsumed:           0
% 4.00/1.00  res_forward_subsumed:                   24
% 4.00/1.00  res_backward_subsumed:                  0
% 4.00/1.00  res_forward_subsumption_resolution:     3
% 4.00/1.00  res_backward_subsumption_resolution:    0
% 4.00/1.00  res_clause_to_clause_subsumption:       6360
% 4.00/1.00  res_orphan_elimination:                 0
% 4.00/1.00  res_tautology_del:                      76
% 4.00/1.00  res_num_eq_res_simplified:              0
% 4.00/1.00  res_num_sel_changes:                    0
% 4.00/1.00  res_moves_from_active_to_pass:          0
% 4.00/1.00  
% 4.00/1.00  ------ Superposition
% 4.00/1.00  
% 4.00/1.00  sup_time_total:                         0.
% 4.00/1.00  sup_time_generating:                    0.
% 4.00/1.00  sup_time_sim_full:                      0.
% 4.00/1.00  sup_time_sim_immed:                     0.
% 4.00/1.00  
% 4.00/1.00  sup_num_of_clauses:                     399
% 4.00/1.00  sup_num_in_active:                      85
% 4.00/1.00  sup_num_in_passive:                     314
% 4.00/1.00  sup_num_of_loops:                       118
% 4.00/1.00  sup_fw_superposition:                   283
% 4.00/1.00  sup_bw_superposition:                   589
% 4.00/1.00  sup_immediate_simplified:               361
% 4.00/1.00  sup_given_eliminated:                   2
% 4.00/1.00  comparisons_done:                       0
% 4.00/1.00  comparisons_avoided:                    0
% 4.00/1.00  
% 4.00/1.00  ------ Simplifications
% 4.00/1.00  
% 4.00/1.00  
% 4.00/1.00  sim_fw_subset_subsumed:                 39
% 4.00/1.00  sim_bw_subset_subsumed:                 17
% 4.00/1.00  sim_fw_subsumed:                        202
% 4.00/1.00  sim_bw_subsumed:                        66
% 4.00/1.00  sim_fw_subsumption_res:                 0
% 4.00/1.00  sim_bw_subsumption_res:                 0
% 4.00/1.00  sim_tautology_del:                      114
% 4.00/1.00  sim_eq_tautology_del:                   11
% 4.00/1.00  sim_eq_res_simp:                        53
% 4.00/1.00  sim_fw_demodulated:                     126
% 4.00/1.00  sim_bw_demodulated:                     0
% 4.00/1.00  sim_light_normalised:                   30
% 4.00/1.00  sim_joinable_taut:                      0
% 4.00/1.00  sim_joinable_simp:                      0
% 4.00/1.00  sim_ac_normalised:                      0
% 4.00/1.00  sim_smt_subsumption:                    0
% 4.00/1.00  
%------------------------------------------------------------------------------
