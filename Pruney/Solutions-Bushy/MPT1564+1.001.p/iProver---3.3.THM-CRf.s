%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1564+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:54 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 379 expanded)
%              Number of clauses        :   86 ( 117 expanded)
%              Number of leaves         :   16 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  688 (2039 expanded)
%              Number of equality atoms :   67 (  67 expanded)
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

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( r2_yellow_0(X0,u1_struct_0(X0))
          & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
        | ~ r1_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,
    ( ? [X0] :
        ( ( ~ r2_yellow_0(X0,u1_struct_0(X0))
          | ~ r1_yellow_0(X0,k1_xboole_0) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ r2_yellow_0(sK6,u1_struct_0(sK6))
        | ~ r1_yellow_0(sK6,k1_xboole_0) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r2_yellow_0(sK6,u1_struct_0(sK6))
      | ~ r1_yellow_0(sK6,k1_xboole_0) )
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f44])).

fof(f73,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK5(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK5(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK3(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK3(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK3(X0,X1))
              & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f47,plain,(
    ! [X0] :
      ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( ~ r2_yellow_0(sK6,u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_789,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r1_lattice3(sK6,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_6,c_25])).

cnf(c_2517,plain,
    ( r1_orders_2(sK6,X0_51,X1_51)
    | ~ r1_lattice3(sK6,X0_52,X0_51)
    | ~ r2_hidden(X1_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_2988,plain,
    ( r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),X0_51)
    | ~ r1_lattice3(sK6,X0_52,sK4(sK6,u1_struct_0(sK6),sK0(sK6)))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_3862,plain,
    ( r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),sK0(sK6))
    | ~ r1_lattice3(sK6,X0_52,sK4(sK6,u1_struct_0(sK6),sK0(sK6)))
    | ~ r2_hidden(sK0(sK6),X0_52)
    | ~ m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_5210,plain,
    ( r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),sK0(sK6))
    | ~ r1_lattice3(sK6,u1_struct_0(sK6),sK4(sK6,u1_struct_0(sK6),sK0(sK6)))
    | ~ r2_hidden(sK0(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3862])).

cnf(c_5211,plain,
    ( r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),sK0(sK6)) = iProver_top
    | r1_lattice3(sK6,u1_struct_0(sK6),sK4(sK6,u1_struct_0(sK6),sK0(sK6))) != iProver_top
    | r2_hidden(sK0(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5210])).

cnf(c_2701,plain,
    ( r1_orders_2(sK6,sK0(sK6),X0_51)
    | ~ r1_lattice3(sK6,X0_52,sK0(sK6))
    | ~ r2_hidden(X0_51,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_3080,plain,
    ( r1_orders_2(sK6,sK0(sK6),sK2(sK6,X0_52,sK0(sK6)))
    | ~ r1_lattice3(sK6,X1_52,sK0(sK6))
    | ~ r2_hidden(sK2(sK6,X0_52,sK0(sK6)),X1_52)
    | ~ m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_3972,plain,
    ( r1_orders_2(sK6,sK0(sK6),sK2(sK6,X0_52,sK0(sK6)))
    | ~ r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6))
    | ~ r2_hidden(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_3973,plain,
    ( r1_orders_2(sK6,sK0(sK6),sK2(sK6,X0_52,sK0(sK6))) = iProver_top
    | r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3972])).

cnf(c_3975,plain,
    ( r1_orders_2(sK6,sK0(sK6),sK2(sK6,k1_xboole_0,sK0(sK6))) = iProver_top
    | r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,k1_xboole_0,sK0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,k1_xboole_0,sK0(sK6)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3973])).

cnf(c_16,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK4(X0,X1,X2))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_543,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r1_lattice3(sK6,X0,sK4(sK6,X0,X1))
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_yellow_0(sK6,X0)
    | r1_lattice3(sK6,X0,sK4(sK6,X0,X1))
    | ~ r1_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_25])).

cnf(c_548,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r1_lattice3(sK6,X0,sK4(sK6,X0,X1))
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_2527,plain,
    ( ~ r1_lattice3(sK6,X0_52,X0_51)
    | r1_lattice3(sK6,X0_52,sK4(sK6,X0_52,X0_51))
    | r2_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_548])).

cnf(c_2696,plain,
    ( r1_lattice3(sK6,X0_52,sK4(sK6,X0_52,sK0(sK6)))
    | ~ r1_lattice3(sK6,X0_52,sK0(sK6))
    | r2_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_2935,plain,
    ( r1_lattice3(sK6,u1_struct_0(sK6),sK4(sK6,u1_struct_0(sK6),sK0(sK6)))
    | ~ r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6))
    | r2_yellow_0(sK6,u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2696])).

cnf(c_2936,plain,
    ( r1_lattice3(sK6,u1_struct_0(sK6),sK4(sK6,u1_struct_0(sK6),sK0(sK6))) = iProver_top
    | r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) != iProver_top
    | r2_yellow_0(sK6,u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_15,plain,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_566,plain,
    ( ~ r1_orders_2(sK6,sK4(sK6,X0,X1),X1)
    | ~ r1_lattice3(sK6,X0,X1)
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_15,c_27])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_yellow_0(sK6,X0)
    | ~ r1_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,sK4(sK6,X0,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_25])).

cnf(c_571,plain,
    ( ~ r1_orders_2(sK6,sK4(sK6,X0,X1),X1)
    | ~ r1_lattice3(sK6,X0,X1)
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_2526,plain,
    ( ~ r1_orders_2(sK6,sK4(sK6,X0_52,X0_51),X0_51)
    | ~ r1_lattice3(sK6,X0_52,X0_51)
    | r2_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_2691,plain,
    ( ~ r1_orders_2(sK6,sK4(sK6,X0_52,sK0(sK6)),sK0(sK6))
    | ~ r1_lattice3(sK6,X0_52,sK0(sK6))
    | r2_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_2932,plain,
    ( ~ r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),sK0(sK6))
    | ~ r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6))
    | r2_yellow_0(sK6,u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2691])).

cnf(c_2933,plain,
    ( r1_orders_2(sK6,sK4(sK6,u1_struct_0(sK6),sK0(sK6)),sK0(sK6)) != iProver_top
    | r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) != iProver_top
    | r2_yellow_0(sK6,u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2932])).

cnf(c_17,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_520,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK4(sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_17,c_27])).

cnf(c_524,plain,
    ( m1_subset_1(sK4(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_yellow_0(sK6,X0)
    | ~ r1_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_25])).

cnf(c_525,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r2_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK4(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_2528,plain,
    ( ~ r1_lattice3(sK6,X0_52,X0_51)
    | r2_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | m1_subset_1(sK4(sK6,X0_52,X0_51),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_525])).

cnf(c_2676,plain,
    ( ~ r1_lattice3(sK6,X0_52,sK0(sK6))
    | r2_yellow_0(sK6,X0_52)
    | m1_subset_1(sK4(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_2850,plain,
    ( ~ r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6))
    | r2_yellow_0(sK6,u1_struct_0(sK6))
    | m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2676])).

cnf(c_2851,plain,
    ( r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) != iProver_top
    | r2_yellow_0(sK6,u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK4(sK6,u1_struct_0(sK6),sK0(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2850])).

cnf(c_21,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_309,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_8,c_28])).

cnf(c_80,plain,
    ( v2_struct_0(sK6)
    | ~ v1_xboole_0(u1_struct_0(sK6))
    | ~ l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_83,plain,
    ( l1_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_311,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_28,c_25,c_80,c_83])).

cnf(c_321,plain,
    ( r2_hidden(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_21,c_311])).

cnf(c_2534,plain,
    ( r2_hidden(X0_51,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_2709,plain,
    ( r2_hidden(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_2764,plain,
    ( r2_hidden(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_2766,plain,
    ( r2_hidden(sK2(sK6,k1_xboole_0,sK0(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK2(sK6,k1_xboole_0,sK0(sK6)),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_2706,plain,
    ( r2_hidden(sK0(sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_2707,plain,
    ( r2_hidden(sK0(sK6),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2706])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_692,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,sK2(sK6,X0,X1))
    | r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_9,c_27])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_yellow_0(sK6,X0)
    | ~ r1_orders_2(sK6,X1,sK2(sK6,X0,X1))
    | ~ r2_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_25])).

cnf(c_697,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,sK2(sK6,X0,X1))
    | r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_2520,plain,
    ( ~ r2_lattice3(sK6,X0_52,X0_51)
    | ~ r1_orders_2(sK6,X0_51,sK2(sK6,X0_52,X0_51))
    | r1_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_697])).

cnf(c_2681,plain,
    ( ~ r2_lattice3(sK6,X0_52,sK0(sK6))
    | ~ r1_orders_2(sK6,sK0(sK6),sK2(sK6,X0_52,sK0(sK6)))
    | r1_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_2682,plain,
    ( r2_lattice3(sK6,X0_52,sK0(sK6)) != iProver_top
    | r1_orders_2(sK6,sK0(sK6),sK2(sK6,X0_52,sK0(sK6))) != iProver_top
    | r1_yellow_0(sK6,X0_52) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2681])).

cnf(c_2684,plain,
    ( r2_lattice3(sK6,k1_xboole_0,sK0(sK6)) != iProver_top
    | r1_orders_2(sK6,sK0(sK6),sK2(sK6,k1_xboole_0,sK0(sK6))) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2682])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_646,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_11,c_27])).

cnf(c_650,plain,
    ( m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_yellow_0(sK6,X0)
    | ~ r2_lattice3(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_25])).

cnf(c_651,plain,
    ( ~ r2_lattice3(sK6,X0,X1)
    | r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_2522,plain,
    ( ~ r2_lattice3(sK6,X0_52,X0_51)
    | r1_yellow_0(sK6,X0_52)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0_52,X0_51),u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_2671,plain,
    ( ~ r2_lattice3(sK6,X0_52,sK0(sK6))
    | r1_yellow_0(sK6,X0_52)
    | m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2522])).

cnf(c_2672,plain,
    ( r2_lattice3(sK6,X0_52,sK0(sK6)) != iProver_top
    | r1_yellow_0(sK6,X0_52) = iProver_top
    | m1_subset_1(sK2(sK6,X0_52,sK0(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2671])).

cnf(c_2674,plain,
    ( r2_lattice3(sK6,k1_xboole_0,sK0(sK6)) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2(sK6,k1_xboole_0,sK0(sK6)),u1_struct_0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_23,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_767,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_23,c_25])).

cnf(c_2519,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_2659,plain,
    ( r2_lattice3(sK6,k1_xboole_0,sK0(sK6))
    | ~ m1_subset_1(sK0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_2660,plain,
    ( r2_lattice3(sK6,k1_xboole_0,sK0(sK6)) = iProver_top
    | m1_subset_1(sK0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_1,plain,
    ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_100,plain,
    ( r1_lattice3(X0,u1_struct_0(X0),sK0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_102,plain,
    ( r1_lattice3(sK6,u1_struct_0(sK6),sK0(sK6)) = iProver_top
    | l1_orders_2(sK6) != iProver_top
    | v1_yellow_0(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_97,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_99,plain,
    ( m1_subset_1(sK0(sK6),u1_struct_0(sK6)) = iProver_top
    | l1_orders_2(sK6) != iProver_top
    | v1_yellow_0(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_24,negated_conjecture,
    ( ~ r2_yellow_0(sK6,u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,k1_xboole_0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,plain,
    ( r2_yellow_0(sK6,u1_struct_0(sK6)) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,plain,
    ( v1_yellow_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5211,c_3975,c_2936,c_2933,c_2851,c_2766,c_2707,c_2684,c_2674,c_2660,c_102,c_99,c_33,c_32,c_31])).


%------------------------------------------------------------------------------
