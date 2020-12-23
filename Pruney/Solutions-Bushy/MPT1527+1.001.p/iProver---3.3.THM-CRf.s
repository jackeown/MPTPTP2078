%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1527+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:47 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  224 (6566 expanded)
%              Number of clauses        :  161 (1717 expanded)
%              Number of leaves         :   13 (1657 expanded)
%              Depth                    :   51
%              Number of atoms          :  962 (48947 expanded)
%              Number of equality atoms :  333 (2460 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f11])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
        & r2_lattice3(X0,X1,X2) )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ( ~ r1_lattice3(X0,X1,X2)
              & r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r1_lattice3(X0,X1,X2) )
            | ( ~ r2_lattice3(X0,X1,X2)
              & r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | sP0(X2,X0,X1) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f20])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ( ~ r1_lattice3(X0,X1,X2)
              & r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              & r1_lattice3(X0,X1,X2) )
            | ( ~ r2_lattice3(X0,X1,X2)
              & r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            | sP0(X2,X0,X1) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ~ r1_lattice3(X0,sK5,sK6)
            & r1_lattice3(X0,k3_xboole_0(sK5,u1_struct_0(X0)),sK6) )
          | ( ~ r1_lattice3(X0,k3_xboole_0(sK5,u1_struct_0(X0)),sK6)
            & r1_lattice3(X0,sK5,sK6) )
          | ( ~ r2_lattice3(X0,sK5,sK6)
            & r2_lattice3(X0,k3_xboole_0(sK5,u1_struct_0(X0)),sK6) )
          | sP0(sK6,X0,sK5) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ( ~ r1_lattice3(X0,X1,X2)
                & r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
              | ( ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
                & r1_lattice3(X0,X1,X2) )
              | ( ~ r2_lattice3(X0,X1,X2)
                & r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
              | sP0(X2,X0,X1) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ( ~ r1_lattice3(sK4,X1,X2)
              & r1_lattice3(sK4,k3_xboole_0(X1,u1_struct_0(sK4)),X2) )
            | ( ~ r1_lattice3(sK4,k3_xboole_0(X1,u1_struct_0(sK4)),X2)
              & r1_lattice3(sK4,X1,X2) )
            | ( ~ r2_lattice3(sK4,X1,X2)
              & r2_lattice3(sK4,k3_xboole_0(X1,u1_struct_0(sK4)),X2) )
            | sP0(X2,sK4,X1) )
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ~ r1_lattice3(sK4,sK5,sK6)
        & r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) )
      | ( ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
        & r1_lattice3(sK4,sK5,sK6) )
      | ( ~ r2_lattice3(sK4,sK5,sK6)
        & r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) )
      | sP0(sK6,sK4,sK5) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f38,f37])).

fof(f60,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
        & r2_lattice3(X0,X1,X2) )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X0)
        & r2_lattice3(X1,X2,X0) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | sP0(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

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
    inference(nnf_transformation,[],[f10])).

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

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | sP0(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,
    ( ~ r1_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | sP0(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,
    ( ~ r1_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | sP0(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_331,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_332,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1506,plain,
    ( ~ r2_lattice3(sK4,X0,X1)
    | r1_orders_2(sK4,sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),X0) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_2390,plain,
    ( ~ r2_lattice3(sK4,X0,sK6)
    | r1_orders_2(sK4,sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK6)
    | ~ m1_subset_1(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),X0) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_21467,plain,
    ( ~ r2_lattice3(sK4,sK5,sK6)
    | r1_orders_2(sK4,sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK6)
    | ~ m1_subset_1(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_367,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_368,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1295,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_352,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_353,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1296,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1300,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1739,plain,
    ( r2_lattice3(sK4,k3_xboole_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,k3_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_1300])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1302,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2)
    | r2_lattice3(X1,X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( sP0(sK6,sK4,sK5)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_600,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_601,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r2_lattice3(sK4,sK5,sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_1289,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1297,plain,
    ( r2_lattice3(sK4,X0,X1) != iProver_top
    | r1_orders_2(sK4,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1858,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1297])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2863,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1858,c_32])).

cnf(c_2864,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2863])).

cnf(c_2873,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_2864])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_303,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_304,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_51,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_54,plain,
    ( l1_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_306,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_29,c_28,c_51,c_54])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_306])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_318,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_418,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_419,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_1360,plain,
    ( r1_lattice3(sK4,X0,sK6)
    | m1_subset_1(sK2(sK4,X0,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_1411,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1412,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_448,plain,
    ( ~ r1_orders_2(X0,X1,sK2(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_449,plain,
    ( ~ r1_orders_2(sK4,X0,sK2(sK4,X1,X0))
    | r1_lattice3(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1386,plain,
    ( ~ r1_orders_2(sK4,sK6,sK2(sK4,X0,sK6))
    | r1_lattice3(sK4,X0,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_1417,plain,
    ( ~ r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6))
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_1418,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_433,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_434,plain,
    ( r1_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1378,plain,
    ( r1_lattice3(sK4,X0,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_1955,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1958,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_8387,plain,
    ( ~ r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8388,plain,
    ( r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8387])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_397,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_28])).

cnf(c_398,plain,
    ( r1_orders_2(sK4,X0,X1)
    | ~ r1_lattice3(sK4,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_2038,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6))
    | ~ r1_lattice3(sK4,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),X1) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2303,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6))
    | ~ r1_lattice3(sK4,X0,sK6)
    | ~ m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),X0) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_8533,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6))
    | ~ r1_lattice3(sK4,sK5,sK6)
    | ~ m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_8534,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8533])).

cnf(c_10258,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2873,c_32,c_318,c_1412,c_1418,c_1958,c_8388,c_8534])).

cnf(c_10259,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_10258])).

cnf(c_1292,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1298,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1907,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1298])).

cnf(c_1291,plain,
    ( r1_lattice3(sK4,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_1724,plain,
    ( r1_lattice3(sK4,k3_xboole_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k3_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1300])).

cnf(c_1299,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1293,plain,
    ( r1_orders_2(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,X2,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1484,plain,
    ( r1_orders_2(sK4,sK6,X0) = iProver_top
    | r1_lattice3(sK4,X1,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_1293])).

cnf(c_1745,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,X0,X1)) = iProver_top
    | r1_lattice3(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1484])).

cnf(c_2242,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,X0,X1)) = iProver_top
    | r1_lattice3(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X2,X3),sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X3) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_1745])).

cnf(c_5732,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(X0,X1),X2)) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),X2) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X3),sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,k3_xboole_0(X0,X1),X2),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_2242])).

cnf(c_9171,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(X0,X1),X2)) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),X2) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,u1_struct_0(sK4)),sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1907,c_5732])).

cnf(c_1290,plain,
    ( r1_orders_2(sK4,X0,sK2(sK4,X1,X0)) != iProver_top
    | r1_lattice3(sK4,X1,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_9187,plain,
    ( r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,u1_struct_0(sK4)),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9171,c_1290])).

cnf(c_9572,plain,
    ( r1_lattice3(sK4,k3_xboole_0(X0,u1_struct_0(sK4)),sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9187,c_32])).

cnf(c_9573,plain,
    ( r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,u1_struct_0(sK4)),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_9572])).

cnf(c_10266,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,X1),sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10259,c_9573])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_382,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_383,plain,
    ( r2_lattice3(sK4,X0,X1)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1294,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_10659,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,X1),sK6) = iProver_top
    | m1_subset_1(sK3(sK4,X0,sK6),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10266,c_1294])).

cnf(c_1350,plain,
    ( r2_lattice3(sK4,X0,sK6)
    | m1_subset_1(sK3(sK4,X0,sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_1351,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | m1_subset_1(sK3(sK4,X0,sK6),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_10992,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,X1),sK6) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10659,c_32,c_1351])).

cnf(c_10998,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_10992])).

cnf(c_11056,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10998,c_32])).

cnf(c_11057,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_11056])).

cnf(c_5730,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,X0,X1)) = iProver_top
    | r1_lattice3(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X2),sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK2(sK4,X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_2242])).

cnf(c_6001,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,X0,X1)) = iProver_top
    | r1_lattice3(sK4,X0,X1) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,u1_struct_0(sK4)),sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1907,c_5730])).

cnf(c_11066,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK6,sK2(sK4,sK5,X0)) = iProver_top
    | r1_lattice3(sK4,sK5,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11057,c_6001])).

cnf(c_11960,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11066,c_1290])).

cnf(c_11963,plain,
    ( r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11960,c_32])).

cnf(c_11964,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_11963])).

cnf(c_11967,plain,
    ( r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11964,c_1297])).

cnf(c_12097,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11967,c_32])).

cnf(c_12098,plain,
    ( r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_12097])).

cnf(c_12104,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_12098])).

cnf(c_12113,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_12104,c_1294])).

cnf(c_12162,plain,
    ( r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12113,c_32])).

cnf(c_12163,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_12162])).

cnf(c_12170,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_12163])).

cnf(c_13433,plain,
    ( r1_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12170,c_32])).

cnf(c_13434,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,X0),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_13433])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_lattice3(X1,k3_xboole_0(X2,u1_struct_0(X1)),X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( sP0(sK6,sK4,sK5)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_638,plain,
    ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_639,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r1_lattice3(sK4,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_1287,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) != iProver_top
    | r2_lattice3(sK4,sK5,sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_13439,plain,
    ( r2_lattice3(sK4,sK5,sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_13434,c_1287])).

cnf(c_14015,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13439,c_32,c_1412,c_1418,c_1958,c_8388,c_8534,c_11960])).

cnf(c_14023,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,sK5,X0)) = iProver_top
    | r1_lattice3(sK4,sK5,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14015,c_6001])).

cnf(c_16631,plain,
    ( r1_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14023,c_1290])).

cnf(c_16634,plain,
    ( r1_lattice3(sK4,sK5,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16631,c_32])).

cnf(c_2245,plain,
    ( r1_orders_2(sK4,sK6,sK2(sK4,k3_xboole_0(X0,X1),X2)) = iProver_top
    | r1_lattice3(sK4,X0,sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_1745])).

cnf(c_5196,plain,
    ( r1_lattice3(sK4,X0,sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2245,c_1290])).

cnf(c_5199,plain,
    ( r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top
    | r1_lattice3(sK4,X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5196,c_32])).

cnf(c_5200,plain,
    ( r1_lattice3(sK4,X0,sK6) != iProver_top
    | r1_lattice3(sK4,k3_xboole_0(X0,X1),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5199])).

cnf(c_20,negated_conjecture,
    ( sP0(sK6,sK4,sK5)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_618,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_619,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | r2_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_1288,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) != iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_5203,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5200,c_1288])).

cnf(c_5256,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5203,c_1297])).

cnf(c_5285,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5256,c_32])).

cnf(c_5286,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5285])).

cnf(c_5295,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_5286])).

cnf(c_7913,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5295,c_318])).

cnf(c_7914,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_7913])).

cnf(c_16638,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,X0,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_16634,c_7914])).

cnf(c_17631,plain,
    ( r2_lattice3(sK4,X0,X1) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r1_orders_2(sK4,sK3(sK4,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_16638])).

cnf(c_17901,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_17631,c_1294])).

cnf(c_17906,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17901,c_32])).

cnf(c_17907,plain,
    ( r2_lattice3(sK4,X0,sK6) = iProver_top
    | r2_lattice3(sK4,sK5,sK6) = iProver_top
    | r2_hidden(sK3(sK4,X0,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_17906])).

cnf(c_17912,plain,
    ( r2_lattice3(sK4,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_17907])).

cnf(c_17919,plain,
    ( r2_lattice3(sK4,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17912])).

cnf(c_16632,plain,
    ( r1_lattice3(sK4,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16631])).

cnf(c_14017,plain,
    ( r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14015])).

cnf(c_8374,plain,
    ( ~ r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4)))
    | r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1366,plain,
    ( r2_lattice3(sK4,X0,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1426,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),k3_xboole_0(sK5,u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_1372,plain,
    ( r2_lattice3(sK4,X0,sK6)
    | ~ r1_orders_2(sK4,sK3(sK4,X0,sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_1427,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_orders_2(sK4,sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_1428,plain,
    ( r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | m1_subset_1(sK3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_19,negated_conjecture,
    ( sP0(sK6,sK4,sK5)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_656,plain,
    ( ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6)
    | sK6 != X2
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_657,plain,
    ( ~ r2_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r2_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,k3_xboole_0(sK5,u1_struct_0(sK4)),sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21467,c_17919,c_16632,c_14017,c_8374,c_1426,c_1427,c_1428,c_657,c_27])).


%------------------------------------------------------------------------------
