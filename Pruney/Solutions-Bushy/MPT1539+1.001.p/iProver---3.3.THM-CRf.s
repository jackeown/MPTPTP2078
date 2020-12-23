%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1539+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:49 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 734 expanded)
%              Number of clauses        :  108 ( 212 expanded)
%              Number of leaves         :   22 ( 180 expanded)
%              Depth                    :   26
%              Number of atoms          : 1157 (5389 expanded)
%              Number of equality atoms :  136 ( 267 expanded)
%              Maximal formula depth    :   13 (   8 average)
%              Maximal clause size      :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK9(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK8(X0,X1,X2))
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK9(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK9(X0,X1))
              & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f47,f49,f48])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK2(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK2(X0,X4))
        & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
        & r2_lattice3(X0,X1,sK1(X0,X2))
        & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK0(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK0(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK1(X0,X2))
                & r2_lattice3(X0,sK0(X0),sK1(X0,X2))
                & m1_subset_1(sK1(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK0(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK2(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK2(X0,X4))
              & m1_subset_1(sK2(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f55,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK2(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK2(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_orders_2(X1)
        & v3_lattice3(X1)
        & v5_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r1_lattice3(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r1_lattice3(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_lattice3(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_lattice3(X1,X2,sK5(X0,X1,X2))
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r1_lattice3(X1,X2,sK5(X0,X1,X2))
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ r1_lattice3(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow_0(X1,X2))
      | ~ r1_lattice3(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f11,plain,(
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
    inference(flattening,[],[f11])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK2(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK5(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK7(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_lattice3(X0,X1,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK7(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK7(X0,X1))
              & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f42,f44,f43])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK6(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( r2_yellow_0(X0,X1)
            & r1_yellow_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
     => ( ~ r2_yellow_0(X0,sK11)
        | ~ r1_yellow_0(X0,sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_yellow_0(sK10,X1)
          | ~ r1_yellow_0(sK10,X1) )
      & l1_orders_2(sK10)
      & v3_lattice3(sK10)
      & v5_orders_2(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r2_yellow_0(sK10,sK11)
      | ~ r1_yellow_0(sK10,sK11) )
    & l1_orders_2(sK10)
    & v3_lattice3(sK10)
    & v5_orders_2(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f22,f52,f51])).

fof(f88,plain,
    ( ~ r2_yellow_0(sK10,sK11)
    | ~ r1_yellow_0(sK10,sK11) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v3_lattice3(sK10) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v5_orders_2(sK10) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_324,plain,
    ( ~ r1_lattice3(X0_53,X0_54,X0_55)
    | ~ r1_orders_2(X0_53,sK8(X0_53,X0_54,X0_55),X0_55)
    | r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_13,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_335,plain,
    ( ~ r2_lattice3(X0_53,X0_54,X0_55)
    | r1_orders_2(X0_53,X1_55,X0_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_344,plain,
    ( r2_lattice3(X0_53,X0_54,sK2(X0_53,X0_54))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3225,plain,
    ( r1_orders_2(X0_53,X0_55,sK2(X0_53,X0_54))
    | ~ r2_hidden(X0_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_335,c_344])).

cnf(c_5,plain,
    ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_343,plain,
    ( m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3874,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ r2_hidden(X0_55,X0_54)
    | r1_orders_2(X0_53,X0_55,sK2(X0_53,X0_54))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3225,c_343])).

cnf(c_3875,plain,
    ( r1_orders_2(X0_53,X0_55,sK2(X0_53,X0_54))
    | ~ r2_hidden(X0_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(renaming,[status(thm)],[c_3874])).

cnf(c_4224,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | r2_yellow_0(X0_53,X0_54)
    | ~ r2_hidden(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),X1_54)
    | ~ m1_subset_1(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_324,c_3875])).

cnf(c_26,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_322,plain,
    ( ~ r1_lattice3(X0_53,X0_54,X0_55)
    | r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | m1_subset_1(sK8(X0_53,X0_54,X0_55),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1552,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | r2_yellow_0(X0_53,X0_54)
    | m1_subset_1(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_20325,plain,
    ( ~ r2_hidden(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),X1_54)
    | r2_yellow_0(X0_53,X0_54)
    | ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4224,c_1552])).

cnf(c_20326,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | r2_yellow_0(X0_53,X0_54)
    | ~ r2_hidden(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),X1_54)
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(renaming,[status(thm)],[c_20325])).

cnf(c_20338,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | r2_yellow_0(X0_53,X0_54)
    | ~ r2_hidden(sK8(X0_53,X0_54,sK2(X0_53,X1_54)),X1_54)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20326,c_343])).

cnf(c_14,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r2_hidden(X2,a_2_0_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_334,plain,
    ( ~ r1_lattice3(X0_53,X0_54,X0_55)
    | r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_20363,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK8(X1_53,X1_54,sK2(X1_53,a_2_0_yellow_0(X0_53,X0_54))))
    | ~ r1_lattice3(X1_53,X1_54,sK2(X1_53,a_2_0_yellow_0(X0_53,X0_54)))
    | r2_yellow_0(X1_53,X1_54)
    | ~ m1_subset_1(sK8(X1_53,X1_54,sK2(X1_53,a_2_0_yellow_0(X0_53,X0_54))),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ v5_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ v3_lattice3(X1_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_20338,c_334])).

cnf(c_25,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X1,sK8(X0,X1,X2))
    | r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_323,plain,
    ( ~ r1_lattice3(X0_53,X0_54,X0_55)
    | r1_lattice3(X0_53,X0_54,sK8(X0_53,X0_54,X0_55))
    | r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_21110,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)))
    | r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK8(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54))),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_20363,c_323])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_342,plain,
    ( r1_lattice3(X0_53,X0_54,X0_55)
    | ~ r1_orders_2(X0_53,X0_55,sK3(X0_53,X0_54,X0_55))
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,sK2(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_345,plain,
    ( ~ r2_lattice3(X0_53,X0_54,X0_55)
    | r1_orders_2(X0_53,sK2(X0_53,X0_54),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1880,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | ~ r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54)))
    | ~ m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_342,c_345])).

cnf(c_938,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55) != iProver_top
    | r1_orders_2(X0_53,sK2(X0_53,X0_54),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_941,plain,
    ( r1_lattice3(X0_53,X0_54,X0_55) = iProver_top
    | r1_orders_2(X0_53,X0_55,sK3(X0_53,X0_54,X0_55)) != iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_2024,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54))) != iProver_top
    | m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_941])).

cnf(c_8,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_340,plain,
    ( r1_lattice3(X0_53,X0_54,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | m1_subset_1(sK3(X0_53,X0_54,X0_55),u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1403,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_1404,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53)) = iProver_top
    | m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_1881,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54))) != iProver_top
    | m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,X1_54)),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1880])).

cnf(c_3858,plain,
    ( r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54))) != iProver_top
    | r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2024,c_1404,c_1881])).

cnf(c_3859,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54))) != iProver_top
    | m1_subset_1(sK2(X0_53,X1_54),u1_struct_0(X0_53)) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3858])).

cnf(c_940,plain,
    ( m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_3869,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54)) = iProver_top
    | r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54))) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3859,c_940])).

cnf(c_3870,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | ~ r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54)))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3869])).

cnf(c_5583,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,X1_54))
    | ~ r2_lattice3(X0_53,X1_54,sK3(X0_53,X0_54,sK2(X0_53,X1_54)))
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1880,c_3870])).

cnf(c_9,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_339,plain,
    ( ~ r1_lattice3(X0_53,X0_54,X0_55)
    | r1_orders_2(X0_53,X0_55,X1_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_15,plain,
    ( r1_lattice3(X0,X1,sK5(X2,X0,X1))
    | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X1))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_333,plain,
    ( r1_lattice3(X0_53,X0_54,sK5(X0_55,X0_53,X0_54))
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3249,plain,
    ( r1_orders_2(X0_53,sK5(X0_55,X0_53,X0_54),X1_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | ~ m1_subset_1(sK5(X0_55,X0_53,X0_54),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_339,c_333])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | m1_subset_1(sK5(X0_55,X0_53,X0_54),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_5619,plain,
    ( ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | ~ r2_hidden(X1_55,X0_54)
    | r1_orders_2(X0_53,sK5(X0_55,X0_53,X0_54),X1_55)
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3249,c_331])).

cnf(c_5620,plain,
    ( r1_orders_2(X0_53,sK5(X0_55,X0_53,X0_54),X1_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(renaming,[status(thm)],[c_5619])).

cnf(c_351,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_350,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1751,plain,
    ( X0_55 != X1_55
    | X1_55 = X0_55 ),
    inference(resolution,[status(thm)],[c_351,c_350])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_lattice3(X1)
    | sK5(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53)
    | sK5(X0_55,X0_53,X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2780,plain,
    ( ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53)
    | X0_55 = sK5(X0_55,X0_53,X0_54) ),
    inference(resolution,[status(thm)],[c_1751,c_332])).

cnf(c_352,plain,
    ( ~ r1_orders_2(X0_53,X0_55,X1_55)
    | r1_orders_2(X0_53,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_2774,plain,
    ( ~ r1_orders_2(X0_53,X0_55,X1_55)
    | r1_orders_2(X0_53,X2_55,X1_55)
    | X2_55 != X0_55 ),
    inference(resolution,[status(thm)],[c_352,c_350])).

cnf(c_2968,plain,
    ( r1_orders_2(X0_53,X0_55,X1_55)
    | ~ r1_orders_2(X0_53,sK5(X0_55,X1_53,X0_54),X1_55)
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X1_53,X0_54))
    | v2_struct_0(X1_53)
    | ~ v5_orders_2(X1_53)
    | ~ l1_orders_2(X1_53)
    | ~ v3_lattice3(X1_53) ),
    inference(resolution,[status(thm)],[c_2780,c_2774])).

cnf(c_6478,plain,
    ( r1_orders_2(X0_53,X0_55,X1_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ r2_hidden(X0_55,a_2_0_yellow_0(X0_53,X0_54))
    | ~ m1_subset_1(X1_55,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_5620,c_2968])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK4(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_337,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55)
    | r2_hidden(sK4(X0_53,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_6819,plain,
    ( r2_lattice3(X0_53,a_2_0_yellow_0(X1_53,X0_54),X0_55)
    | r1_orders_2(X1_53,sK4(X0_53,a_2_0_yellow_0(X1_53,X0_54),X0_55),X1_55)
    | ~ r2_hidden(X1_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_55,u1_struct_0(X1_53))
    | v2_struct_0(X1_53)
    | ~ v5_orders_2(X1_53)
    | ~ l1_orders_2(X0_53)
    | ~ l1_orders_2(X1_53)
    | ~ v3_lattice3(X1_53) ),
    inference(resolution,[status(thm)],[c_6478,c_337])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_338,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55)
    | ~ r1_orders_2(X0_53,sK4(X0_53,X0_54,X0_55),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_14337,plain,
    ( r2_lattice3(X0_53,a_2_0_yellow_0(X0_53,X0_54),X0_55)
    | ~ r2_hidden(X0_55,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_6819,c_338])).

cnf(c_15314,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54)))
    | ~ r2_hidden(sK3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54))),X1_54)
    | ~ m1_subset_1(sK3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54))),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_5583,c_14337])).

cnf(c_16102,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54)))
    | ~ r2_hidden(sK3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54))),X1_54)
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_15314,c_340])).

cnf(c_16381,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54)))
    | ~ r2_hidden(sK3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X1_54))),X1_54)
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16102,c_343])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_341,plain,
    ( r1_lattice3(X0_53,X0_54,X0_55)
    | r2_hidden(sK3(X0_53,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_16410,plain,
    ( r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)))
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_16381,c_341])).

cnf(c_21506,plain,
    ( r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK8(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54))),u1_struct_0(X0_53))
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21110,c_16410])).

cnf(c_21519,plain,
    ( r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK8(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54))),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21506,c_343])).

cnf(c_21544,plain,
    ( ~ r1_lattice3(X0_53,X0_54,sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)))
    | r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(resolution,[status(thm)],[c_21519,c_322])).

cnf(c_21549,plain,
    ( r2_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK2(X0_53,a_2_0_yellow_0(X0_53,X0_54)),u1_struct_0(X0_53))
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21544,c_16410])).

cnf(c_21561,plain,
    ( r2_yellow_0(X0_53,X0_54)
    | v2_struct_0(X0_53)
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21549,c_343])).

cnf(c_21563,plain,
    ( r2_yellow_0(sK10,sK11)
    | v2_struct_0(sK10)
    | ~ v5_orders_2(sK10)
    | ~ l1_orders_2(sK10)
    | ~ v3_lattice3(sK10) ),
    inference(instantiation,[status(thm)],[c_21561])).

cnf(c_20,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_328,plain,
    ( ~ r2_lattice3(X0_53,X0_54,X0_55)
    | r1_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | m1_subset_1(sK6(X0_53,X0_54,X0_55),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_955,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55) != iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK6(X0_53,X0_54,X0_55),u1_struct_0(X0_53)) = iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK6(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_329,plain,
    ( ~ r2_lattice3(X0_53,X0_54,X0_55)
    | r2_lattice3(X0_53,X0_54,sK6(X0_53,X0_54,X0_55))
    | r1_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_954,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55) != iProver_top
    | r2_lattice3(X0_53,X0_54,sK6(X0_53,X0_54,X0_55)) = iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_18,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
    | r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_330,plain,
    ( ~ r2_lattice3(X0_53,X0_54,X0_55)
    | ~ r1_orders_2(X0_53,X0_55,sK6(X0_53,X0_54,X0_55))
    | r1_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(X0_55,u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_953,plain,
    ( r2_lattice3(X0_53,X0_54,X0_55) != iProver_top
    | r1_orders_2(X0_53,X0_55,sK6(X0_53,X0_54,X0_55)) != iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_2498,plain,
    ( r2_lattice3(X0_53,X0_54,sK6(X0_53,X1_54,sK2(X0_53,X0_54))) != iProver_top
    | r2_lattice3(X0_53,X1_54,sK2(X0_53,X0_54)) != iProver_top
    | r1_yellow_0(X0_53,X1_54) = iProver_top
    | m1_subset_1(sK6(X0_53,X1_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_953])).

cnf(c_373,plain,
    ( m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_5030,plain,
    ( m1_subset_1(sK6(X0_53,X1_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | r1_yellow_0(X0_53,X1_54) = iProver_top
    | r2_lattice3(X0_53,X1_54,sK2(X0_53,X0_54)) != iProver_top
    | r2_lattice3(X0_53,X0_54,sK6(X0_53,X1_54,sK2(X0_53,X0_54))) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_373])).

cnf(c_5031,plain,
    ( r2_lattice3(X0_53,X0_54,sK6(X0_53,X1_54,sK2(X0_53,X0_54))) != iProver_top
    | r2_lattice3(X0_53,X1_54,sK2(X0_53,X0_54)) != iProver_top
    | r1_yellow_0(X0_53,X1_54) = iProver_top
    | m1_subset_1(sK6(X0_53,X1_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5030])).

cnf(c_5043,plain,
    ( r2_lattice3(X0_53,X0_54,sK2(X0_53,X0_54)) != iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(sK6(X0_53,X0_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_5031])).

cnf(c_370,plain,
    ( r2_lattice3(X0_53,X0_54,sK2(X0_53,X0_54)) = iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_5048,plain,
    ( m1_subset_1(sK6(X0_53,X0_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5043,c_370,c_373])).

cnf(c_5049,plain,
    ( r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(sK6(X0_53,X0_54,sK2(X0_53,X0_54)),u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5048])).

cnf(c_5292,plain,
    ( r2_lattice3(X0_53,X0_54,sK2(X0_53,X0_54)) != iProver_top
    | r1_yellow_0(X0_53,X0_54) = iProver_top
    | m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53)) != iProver_top
    | v5_orders_2(X0_53) != iProver_top
    | l1_orders_2(X0_53) != iProver_top
    | v3_lattice3(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_5049])).

cnf(c_5347,plain,
    ( ~ r2_lattice3(X0_53,X0_54,sK2(X0_53,X0_54))
    | r1_yellow_0(X0_53,X0_54)
    | ~ m1_subset_1(sK2(X0_53,X0_54),u1_struct_0(X0_53))
    | ~ v5_orders_2(X0_53)
    | ~ l1_orders_2(X0_53)
    | ~ v3_lattice3(X0_53) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5292])).

cnf(c_5349,plain,
    ( ~ r2_lattice3(sK10,sK11,sK2(sK10,sK11))
    | r1_yellow_0(sK10,sK11)
    | ~ m1_subset_1(sK2(sK10,sK11),u1_struct_0(sK10))
    | ~ v5_orders_2(sK10)
    | ~ l1_orders_2(sK10)
    | ~ v3_lattice3(sK10) ),
    inference(instantiation,[status(thm)],[c_5347])).

cnf(c_374,plain,
    ( m1_subset_1(sK2(sK10,sK11),u1_struct_0(sK10))
    | ~ l1_orders_2(sK10)
    | ~ v3_lattice3(sK10) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_371,plain,
    ( r2_lattice3(sK10,sK11,sK2(sK10,sK11))
    | ~ l1_orders_2(sK10)
    | ~ v3_lattice3(sK10) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_30,negated_conjecture,
    ( ~ r2_yellow_0(sK10,sK11)
    | ~ r1_yellow_0(sK10,sK11) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK10) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,negated_conjecture,
    ( v3_lattice3(sK10) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( v5_orders_2(sK10) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21563,c_5349,c_374,c_371,c_30,c_31,c_32,c_33,c_34])).


%------------------------------------------------------------------------------
