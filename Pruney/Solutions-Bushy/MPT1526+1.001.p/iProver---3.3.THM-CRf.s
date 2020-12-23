%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1526+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:46 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 524 expanded)
%              Number of clauses        :   76 ( 112 expanded)
%              Number of leaves         :   10 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  560 (4141 expanded)
%              Number of equality atoms :   78 (  78 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => ! [X3] :
                      ( ( r2_lattice3(X0,X3,X1)
                       => r2_lattice3(X0,X3,X2) )
                      & ( r1_lattice3(X0,X3,X2)
                       => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X3,X2)
            & r2_lattice3(X0,X3,X1) )
          | ( ~ r1_lattice3(X0,X3,X1)
            & r1_lattice3(X0,X3,X2) ) )
     => ( ( ~ r2_lattice3(X0,sK5,X2)
          & r2_lattice3(X0,sK5,X1) )
        | ( ~ r1_lattice3(X0,sK5,X1)
          & r1_lattice3(X0,sK5,X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(X0,X3,X2)
                & r2_lattice3(X0,X3,X1) )
              | ( ~ r1_lattice3(X0,X3,X1)
                & r1_lattice3(X0,X3,X2) ) )
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ~ r2_lattice3(X0,X3,sK4)
              & r2_lattice3(X0,X3,X1) )
            | ( ~ r1_lattice3(X0,X3,X1)
              & r1_lattice3(X0,X3,sK4) ) )
        & r1_orders_2(X0,X1,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(X0,X3,X2)
                  & r2_lattice3(X0,X3,sK3) )
                | ( ~ r1_lattice3(X0,X3,sK3)
                  & r1_lattice3(X0,X3,X2) ) )
            & r1_orders_2(X0,sK3,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X3,X2)
                      & r2_lattice3(X0,X3,X1) )
                    | ( ~ r1_lattice3(X0,X3,X1)
                      & r1_lattice3(X0,X3,X2) ) )
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK2,X3,X2)
                    & r2_lattice3(sK2,X3,X1) )
                  | ( ~ r1_lattice3(sK2,X3,X1)
                    & r1_lattice3(sK2,X3,X2) ) )
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ( ~ r2_lattice3(sK2,sK5,sK4)
        & r2_lattice3(sK2,sK5,sK3) )
      | ( ~ r1_lattice3(sK2,sK5,sK3)
        & r1_lattice3(sK2,sK5,sK4) ) )
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f25,f24,f23,f22])).

fof(f36,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

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

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | r1_lattice3(sK2,sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | ~ r1_lattice3(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,
    ( r2_lattice3(sK2,sK5,sK3)
    | ~ r1_lattice3(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,
    ( r2_lattice3(sK2,sK5,sK3)
    | r1_lattice3(sK2,sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_182,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X0)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_17])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,X2,X1)
    | ~ r1_orders_2(sK2,X2,X0)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_16])).

cnf(c_185,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X0)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_1551,plain,
    ( ~ r1_orders_2(sK2,X0_43,X1_43)
    | ~ r1_orders_2(sK2,X2_43,X0_43)
    | r1_orders_2(sK2,X2_43,X1_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X2_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_1710,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,sK5,X1_43))
    | ~ r1_orders_2(sK2,X0_43,sK4)
    | ~ r1_orders_2(sK2,sK4,sK0(sK2,sK5,X1_43))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,sK5,X1_43),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1711,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,sK5,X1_43)) = iProver_top
    | r1_orders_2(sK2,X0_43,sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,sK5,X1_43)) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,X1_43),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_1713,plain,
    ( r1_orders_2(sK2,sK3,sK0(sK2,sK5,sK3)) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top
    | r1_orders_2(sK2,sK4,sK0(sK2,sK5,sK3)) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1711])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_276,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_3,c_16])).

cnf(c_1546,plain,
    ( r1_orders_2(sK2,X0_43,X1_43)
    | ~ r1_lattice3(sK2,X0_44,X0_43)
    | ~ r2_hidden(X1_43,X0_44)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_1648,plain,
    ( r1_orders_2(sK2,X0_43,sK0(sK2,X0_44,X1_43))
    | ~ r1_lattice3(sK2,X0_44,X0_43)
    | ~ r2_hidden(sK0(sK2,X0_44,X1_43),X0_44)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2,X0_44,X1_43),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1684,plain,
    ( r1_orders_2(sK2,sK4,sK0(sK2,sK5,X0_43))
    | ~ r1_lattice3(sK2,sK5,sK4)
    | ~ r2_hidden(sK0(sK2,sK5,X0_43),sK5)
    | ~ m1_subset_1(sK0(sK2,sK5,X0_43),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_1685,plain,
    ( r1_orders_2(sK2,sK4,sK0(sK2,sK5,X0_43)) = iProver_top
    | r1_lattice3(sK2,sK5,sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK5,X0_43),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,X0_43),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_1687,plain,
    ( r1_orders_2(sK2,sK4,sK0(sK2,sK5,sK3)) = iProver_top
    | r1_lattice3(sK2,sK5,sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK5,sK3),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_1658,plain,
    ( ~ r1_orders_2(sK2,X0_43,sK3)
    | r1_orders_2(sK2,X0_43,sK4)
    | ~ r1_orders_2(sK2,sK3,sK4)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1671,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK3)
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK4)
    | ~ r1_orders_2(sK2,sK3,sK4)
    | ~ m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_1672,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK4) = iProver_top
    | r1_orders_2(sK2,sK3,sK4) != iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1671])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_214,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_7,c_16])).

cnf(c_1550,plain,
    ( ~ r2_lattice3(sK2,X0_44,X0_43)
    | r1_orders_2(sK2,X1_43,X0_43)
    | ~ r2_hidden(X1_43,X0_44)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_214])).

cnf(c_1661,plain,
    ( ~ r2_lattice3(sK2,sK5,X0_43)
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),X0_43)
    | ~ r2_hidden(sK1(sK2,sK5,sK4),sK5)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_1667,plain,
    ( r2_lattice3(sK2,sK5,X0_43) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),X0_43) = iProver_top
    | r2_hidden(sK1(sK2,sK5,sK4),sK5) != iProver_top
    | m1_subset_1(X0_43,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1661])).

cnf(c_1669,plain,
    ( r2_lattice3(sK2,sK5,sK3) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK5,sK4),sK5) != iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_248,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_16])).

cnf(c_1548,plain,
    ( r2_lattice3(sK2,X0_44,X0_43)
    | r2_hidden(sK1(sK2,X0_44,X0_43),X0_44)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_248])).

cnf(c_1645,plain,
    ( r2_lattice3(sK2,sK5,sK4)
    | r2_hidden(sK1(sK2,sK5,sK4),sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1646,plain,
    ( r2_lattice3(sK2,sK5,sK4) = iProver_top
    | r2_hidden(sK1(sK2,sK5,sK4),sK5) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_262,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_4,c_16])).

cnf(c_1547,plain,
    ( r2_lattice3(sK2,X0_44,X0_43)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_44,X0_43),X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_262])).

cnf(c_1642,plain,
    ( r2_lattice3(sK2,sK5,sK4)
    | ~ r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_1643,plain,
    ( r2_lattice3(sK2,sK5,sK4) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK5,sK4),sK4) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_234,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1549,plain,
    ( r2_lattice3(sK2,X0_44,X0_43)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_44,X0_43),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_234])).

cnf(c_1639,plain,
    ( r2_lattice3(sK2,sK5,sK4)
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_1640,plain,
    ( r2_lattice3(sK2,sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_10,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | r1_lattice3(sK2,sK5,sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_792,plain,
    ( r1_lattice3(sK2,sK5,sK4)
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_234])).

cnf(c_793,plain,
    ( r1_lattice3(sK2,sK5,sK4) = iProver_top
    | m1_subset_1(sK1(sK2,sK5,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_779,plain,
    ( r1_lattice3(sK2,sK5,sK4)
    | r2_hidden(sK1(sK2,sK5,sK4),sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_248])).

cnf(c_780,plain,
    ( r1_lattice3(sK2,sK5,sK4) = iProver_top
    | r2_hidden(sK1(sK2,sK5,sK4),sK5) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_9,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | ~ r1_lattice3(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_324,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_0,c_16])).

cnf(c_552,plain,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | ~ r1_orders_2(sK2,sK3,sK0(sK2,sK5,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_324])).

cnf(c_553,plain,
    ( r2_lattice3(sK2,sK5,sK4) != iProver_top
    | r1_orders_2(sK2,sK3,sK0(sK2,sK5,sK3)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_11,negated_conjecture,
    ( r2_lattice3(sK2,sK5,sK3)
    | ~ r1_lattice3(sK2,sK5,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_539,plain,
    ( r2_lattice3(sK2,sK5,sK3)
    | ~ r1_orders_2(sK2,sK3,sK0(sK2,sK5,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_324])).

cnf(c_540,plain,
    ( r2_lattice3(sK2,sK5,sK3) = iProver_top
    | r1_orders_2(sK2,sK3,sK0(sK2,sK5,sK3)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_296,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_2,c_16])).

cnf(c_526,plain,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_296])).

cnf(c_527,plain,
    ( r2_lattice3(sK2,sK5,sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_310,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_16])).

cnf(c_513,plain,
    ( ~ r2_lattice3(sK2,sK5,sK4)
    | r2_hidden(sK0(sK2,sK5,sK3),sK5)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_9,c_310])).

cnf(c_514,plain,
    ( r2_lattice3(sK2,sK5,sK4) != iProver_top
    | r2_hidden(sK0(sK2,sK5,sK3),sK5) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_500,plain,
    ( r2_lattice3(sK2,sK5,sK3)
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_296])).

cnf(c_501,plain,
    ( r2_lattice3(sK2,sK5,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK5,sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_487,plain,
    ( r2_lattice3(sK2,sK5,sK3)
    | r2_hidden(sK0(sK2,sK5,sK3),sK5)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_310])).

cnf(c_488,plain,
    ( r2_lattice3(sK2,sK5,sK3) = iProver_top
    | r2_hidden(sK0(sK2,sK5,sK3),sK5) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_25,plain,
    ( r2_lattice3(sK2,sK5,sK4) != iProver_top
    | r1_lattice3(sK2,sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,negated_conjecture,
    ( r2_lattice3(sK2,sK5,sK3)
    | r1_lattice3(sK2,sK5,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,plain,
    ( r2_lattice3(sK2,sK5,sK3) = iProver_top
    | r1_lattice3(sK2,sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,plain,
    ( r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_20,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1713,c_1687,c_1672,c_1669,c_1646,c_1643,c_1640,c_793,c_780,c_553,c_540,c_527,c_514,c_501,c_488,c_25,c_23,c_22,c_21,c_20])).


%------------------------------------------------------------------------------
