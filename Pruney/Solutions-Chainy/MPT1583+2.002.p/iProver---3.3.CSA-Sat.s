%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:59 EST 2020

% Result     : CounterSatisfiable 1.81s
% Output     : Saturation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  184 (1937 expanded)
%              Number of clauses        :  127 ( 485 expanded)
%              Number of leaves         :   17 ( 547 expanded)
%              Depth                    :   20
%              Number of atoms          :  723 (16136 expanded)
%              Number of equality atoms :  219 (1844 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ~ v2_struct_0(X1)
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ( ~ r2_lattice3(X1,X2,X4)
              & r2_lattice3(X0,X2,X3) )
            | ( ~ r1_lattice3(X1,X2,X4)
              & r1_lattice3(X0,X2,X3) ) )
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ( ( ~ r2_lattice3(X1,X2,sK6)
            & r2_lattice3(X0,X2,X3) )
          | ( ~ r1_lattice3(X1,X2,sK6)
            & r1_lattice3(X0,X2,X3) ) )
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ( ( ~ r2_lattice3(X1,X2,X4)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X1,X2,X4)
                  & r1_lattice3(X0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ( ~ r2_lattice3(X1,sK4,X4)
                & r2_lattice3(X0,sK4,sK5) )
              | ( ~ r1_lattice3(X1,sK4,X4)
                & r1_lattice3(X0,sK4,sK5) ) )
            & sK5 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & ~ v2_struct_0(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r2_lattice3(sK3,X2,X4)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(sK3,X2,X4)
                    & r1_lattice3(X0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK3)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ( ( ~ r2_lattice3(X1,X2,X4)
                        & r2_lattice3(X0,X2,X3) )
                      | ( ~ r1_lattice3(X1,X2,X4)
                        & r1_lattice3(X0,X2,X3) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(sK2,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK2,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ( ~ r2_lattice3(sK3,sK4,sK6)
        & r2_lattice3(sK2,sK4,sK5) )
      | ( ~ r1_lattice3(sK3,sK4,sK6)
        & r1_lattice3(sK2,sK4,sK5) ) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f35,f34,f33,f32])).

fof(f50,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_207,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_206,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_204,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2539,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_419,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_420,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_2524,plain,
    ( r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_2915,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2524])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_232,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_282,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_21])).

cnf(c_283,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_285,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_20])).

cnf(c_313,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_285])).

cnf(c_314,plain,
    ( r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_2530,plain,
    ( r2_hidden(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_314])).

cnf(c_2909,plain,
    ( r2_hidden(X0_45,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2530])).

cnf(c_4226,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2909])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2531,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2908,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_16,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2533,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2923,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2908,c_2533])).

cnf(c_7,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_398,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_399,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_2525,plain,
    ( r1_orders_2(sK2,X0_45,X1_45)
    | ~ r1_lattice3(sK2,X0_46,X0_45)
    | ~ r2_hidden(X1_45,X0_46)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_2914,plain,
    ( r1_orders_2(sK2,X0_45,X1_45) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) != iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2525])).

cnf(c_3705,plain,
    ( r1_orders_2(sK2,sK6,X0_45) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | r2_hidden(X0_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_2914])).

cnf(c_4222,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK6) != iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_3705])).

cnf(c_4792,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4226,c_4222])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_449,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_450,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_2522,plain,
    ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45))
    | r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_450])).

cnf(c_2917,plain,
    ( r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_5650,plain,
    ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4792,c_2917])).

cnf(c_5655,plain,
    ( r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_lattice3(sK2,X0_46,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5650,c_2923])).

cnf(c_5656,plain,
    ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5655])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_353,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_354,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_2528,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_2911,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2528])).

cnf(c_3871,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_2909])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_332,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_333,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_2529,plain,
    ( ~ r2_lattice3(sK2,X0_46,X0_45)
    | r1_orders_2(sK2,X1_45,X0_45)
    | ~ r2_hidden(X1_45,X0_46)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_2910,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) != iProver_top
    | r1_orders_2(sK2,X1_45,X0_45) = iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_3449,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,X0_45,sK6) = iProver_top
    | r2_hidden(X0_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_2910])).

cnf(c_3869,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X1_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_3449])).

cnf(c_4691,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3871,c_3869])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_383,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_384,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_2526,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_2913,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2526])).

cnf(c_5499,plain,
    ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4691,c_2913])).

cnf(c_5504,plain,
    ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r2_lattice3(sK2,X0_46,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5499,c_2923])).

cnf(c_5505,plain,
    ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5504])).

cnf(c_4224,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X1_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
    | r2_hidden(sK0(sK2,X1_46,X0_45),X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_3449])).

cnf(c_4985,plain,
    ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4226,c_4224])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_434,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_435,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_2523,plain,
    ( r1_lattice3(sK2,X0_46,X0_45)
    | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_2916,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2523])).

cnf(c_4984,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_4224])).

cnf(c_4791,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_4222])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_368,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_369,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_2527,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_2912,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2527])).

cnf(c_4690,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_3869])).

cnf(c_3867,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X1_46,sK6) != iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_3705])).

cnf(c_4568,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3871,c_3867])).

cnf(c_4567,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_3867])).

cnf(c_4225,plain,
    ( r2_lattice3(sK2,X0_46,sK0(sK2,X1_46,X0_45)) != iProver_top
    | r1_orders_2(sK2,X1_45,sK0(sK2,X1_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2910])).

cnf(c_4223,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),X1_45) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_45)) != iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2914])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2538,plain,
    ( ~ r2_hidden(X0_45,X0_46)
    | m1_subset_1(X0_45,X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2902,plain,
    ( r2_hidden(X0_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2538])).

cnf(c_4047,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_2916,c_2902])).

cnf(c_15,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2534,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2906,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2534])).

cnf(c_2930,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2906,c_2533])).

cnf(c_3546,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r2_hidden(sK6,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_3449])).

cnf(c_3574,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_3546])).

cnf(c_3738,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | r2_hidden(sK6,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_3705])).

cnf(c_3757,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) != iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3738])).

cnf(c_4037,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_3757])).

cnf(c_3870,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
    | r1_orders_2(sK2,X1_45,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_2910])).

cnf(c_3868,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X1_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_2914])).

cnf(c_3283,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_2902])).

cnf(c_3450,plain,
    ( r2_lattice3(sK2,X0_46,sK1(sK2,u1_struct_0(sK2),X0_45)) != iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),X0_45) = iProver_top
    | r1_orders_2(sK2,X1_45,sK1(sK2,u1_struct_0(sK2),X0_45)) = iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_2910])).

cnf(c_3243,plain,
    ( r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_2909])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2535,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2905,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2535])).

cnf(c_2940,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2905,c_2533])).

cnf(c_13,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2536,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2904,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2536])).

cnf(c_2935,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2904,c_2533])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_272,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_19])).

cnf(c_273,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_298,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | ~ l1_orders_2(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_273])).

cnf(c_299,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_464,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_299])).

cnf(c_2521,plain,
    ( r2_hidden(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_2918,plain,
    ( sK2 != sK3
    | r2_hidden(X0_45,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2521])).

cnf(c_12,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2537,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2903,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2537])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2532,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2907,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2532])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:16:23 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/0.98  
% 1.81/0.98  ------  iProver source info
% 1.81/0.98  
% 1.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/0.98  git: non_committed_changes: false
% 1.81/0.98  git: last_make_outside_of_git: false
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     num_symb
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       true
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  ------ Parsing...
% 1.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/0.98  ------ Proving...
% 1.81/0.98  ------ Problem Properties 
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  clauses                                 18
% 1.81/0.98  conjectures                             7
% 1.81/0.98  EPR                                     6
% 1.81/0.98  Horn                                    13
% 1.81/0.98  unary                                   3
% 1.81/0.98  binary                                  6
% 1.81/0.98  lits                                    46
% 1.81/0.98  lits eq                                 2
% 1.81/0.98  fd_pure                                 0
% 1.81/0.98  fd_pseudo                               0
% 1.81/0.98  fd_cond                                 0
% 1.81/0.98  fd_pseudo_cond                          0
% 1.81/0.98  AC symbols                              0
% 1.81/0.98  
% 1.81/0.98  ------ Schedule dynamic 5 is on 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  Current options:
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     none
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       false
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ Proving...
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  % SZS output start Saturation for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  fof(f6,axiom,(
% 1.81/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f18,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(ennf_transformation,[],[f6])).
% 1.81/0.98  
% 1.81/0.98  fof(f19,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(flattening,[],[f18])).
% 1.81/0.98  
% 1.81/0.98  fof(f24,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(nnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f25,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(rectify,[],[f24])).
% 1.81/0.98  
% 1.81/0.98  fof(f26,plain,(
% 1.81/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f27,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f42,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f8,conjecture,(
% 1.81/0.98    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f9,negated_conjecture,(
% 1.81/0.98    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.81/0.98    inference(negated_conjecture,[],[f8])).
% 1.81/0.98  
% 1.81/0.98  fof(f10,plain,(
% 1.81/0.98    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.81/0.98    inference(pure_predicate_removal,[],[f9])).
% 1.81/0.98  
% 1.81/0.98  fof(f11,plain,(
% 1.81/0.98    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.81/0.98    inference(pure_predicate_removal,[],[f10])).
% 1.81/0.98  
% 1.81/0.98  fof(f22,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : ((((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f11])).
% 1.81/0.98  
% 1.81/0.98  fof(f23,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f22])).
% 1.81/0.98  
% 1.81/0.98  fof(f35,plain,(
% 1.81/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (((~r2_lattice3(X1,X2,sK6) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,sK6) & r1_lattice3(X0,X2,X3))) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f34,plain,(
% 1.81/0.98    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (((~r2_lattice3(X1,sK4,X4) & r2_lattice3(X0,sK4,sK5)) | (~r1_lattice3(X1,sK4,X4) & r1_lattice3(X0,sK4,sK5))) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f33,plain,(
% 1.81/0.98    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) => (? [X3,X2] : (? [X4] : (((~r2_lattice3(sK3,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(sK3,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(sK3))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f32,plain,(
% 1.81/0.98    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(sK2,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(sK2,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK2))) & ~v2_struct_0(X1)) & l1_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f36,plain,(
% 1.81/0.98    (((((~r2_lattice3(sK3,sK4,sK6) & r2_lattice3(sK2,sK4,sK5)) | (~r1_lattice3(sK3,sK4,sK6) & r1_lattice3(sK2,sK4,sK5))) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK2))) & ~v2_struct_0(sK3)) & l1_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f35,f34,f33,f32])).
% 1.81/0.98  
% 1.81/0.98  fof(f50,plain,(
% 1.81/0.98    l1_orders_2(sK2)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f3,axiom,(
% 1.81/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f13,plain,(
% 1.81/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.81/0.98    inference(ennf_transformation,[],[f3])).
% 1.81/0.98  
% 1.81/0.98  fof(f14,plain,(
% 1.81/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.81/0.98    inference(flattening,[],[f13])).
% 1.81/0.98  
% 1.81/0.98  fof(f38,plain,(
% 1.81/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f14])).
% 1.81/0.98  
% 1.81/0.98  fof(f5,axiom,(
% 1.81/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f17,plain,(
% 1.81/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(ennf_transformation,[],[f5])).
% 1.81/0.98  
% 1.81/0.98  fof(f40,plain,(
% 1.81/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f17])).
% 1.81/0.98  
% 1.81/0.98  fof(f4,axiom,(
% 1.81/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f15,plain,(
% 1.81/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f4])).
% 1.81/0.98  
% 1.81/0.98  fof(f16,plain,(
% 1.81/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.81/0.98    inference(flattening,[],[f15])).
% 1.81/0.98  
% 1.81/0.98  fof(f39,plain,(
% 1.81/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f16])).
% 1.81/0.98  
% 1.81/0.98  fof(f49,plain,(
% 1.81/0.98    ~v2_struct_0(sK2)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f52,plain,(
% 1.81/0.98    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f54,plain,(
% 1.81/0.98    sK5 = sK6),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f41,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f44,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f7,axiom,(
% 1.81/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f20,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(ennf_transformation,[],[f7])).
% 1.81/0.98  
% 1.81/0.98  fof(f21,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(flattening,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  fof(f28,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(nnf_transformation,[],[f21])).
% 1.81/0.98  
% 1.81/0.98  fof(f29,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(rectify,[],[f28])).
% 1.81/0.98  
% 1.81/0.98  fof(f30,plain,(
% 1.81/0.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f31,plain,(
% 1.81/0.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.81/0.98  
% 1.81/0.98  fof(f46,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f31])).
% 1.81/0.98  
% 1.81/0.98  fof(f45,plain,(
% 1.81/0.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f31])).
% 1.81/0.98  
% 1.81/0.98  fof(f48,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f31])).
% 1.81/0.98  
% 1.81/0.98  fof(f43,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f27])).
% 1.81/0.98  
% 1.81/0.98  fof(f47,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f31])).
% 1.81/0.98  
% 1.81/0.98  fof(f2,axiom,(
% 1.81/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f12,plain,(
% 1.81/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.81/0.98    inference(ennf_transformation,[],[f2])).
% 1.81/0.98  
% 1.81/0.98  fof(f37,plain,(
% 1.81/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f12])).
% 1.81/0.98  
% 1.81/0.98  fof(f55,plain,(
% 1.81/0.98    r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f56,plain,(
% 1.81/0.98    r2_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK3,sK4,sK6)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f57,plain,(
% 1.81/0.98    ~r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f51,plain,(
% 1.81/0.98    ~v2_struct_0(sK3)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f58,plain,(
% 1.81/0.98    ~r2_lattice3(sK3,sK4,sK6) | ~r1_lattice3(sK3,sK4,sK6)),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  fof(f53,plain,(
% 1.81/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.81/0.98    inference(cnf_transformation,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  cnf(c_207,plain,
% 1.81/0.98      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.81/0.98      theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_206,plain,
% 1.81/0.98      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.81/0.98      theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_204,plain,
% 1.81/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.81/0.98      theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2539,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_6,plain,
% 1.81/0.98      ( r1_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_20,negated_conjecture,
% 1.81/0.98      ( l1_orders_2(sK2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_419,plain,
% 1.81/0.98      ( r1_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_420,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0,X1)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.81/0.98      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_419]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2524,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.81/0.98      | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_420]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2915,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2524]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1,plain,
% 1.81/0.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3,plain,
% 1.81/0.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2,plain,
% 1.81/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_232,plain,
% 1.81/0.98      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.81/0.98      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_21,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_282,plain,
% 1.81/0.98      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_232,c_21]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_283,plain,
% 1.81/0.98      ( ~ l1_orders_2(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_282]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_285,plain,
% 1.81/0.98      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.81/0.98      inference(global_propositional_subsumption,[status(thm)],[c_283,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_313,plain,
% 1.81/0.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | u1_struct_0(sK2) != X1 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_285]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_314,plain,
% 1.81/0.98      ( r2_hidden(X0,u1_struct_0(sK2)) | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_313]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2530,plain,
% 1.81/0.98      ( r2_hidden(X0_45,u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_314]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2909,plain,
% 1.81/0.98      ( r2_hidden(X0_45,u1_struct_0(sK2)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2530]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4226,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2915,c_2909]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_18,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2531,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2908,plain,
% 1.81/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_16,negated_conjecture,
% 1.81/0.98      ( sK5 = sK6 ),
% 1.81/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2533,negated_conjecture,
% 1.81/0.98      ( sK5 = sK6 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2923,plain,
% 1.81/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2908,c_2533]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_7,plain,
% 1.81/0.98      ( r1_orders_2(X0,X1,X2)
% 1.81/0.98      | ~ r1_lattice3(X0,X3,X1)
% 1.81/0.98      | ~ r2_hidden(X2,X3)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_398,plain,
% 1.81/0.98      ( r1_orders_2(X0,X1,X2)
% 1.81/0.98      | ~ r1_lattice3(X0,X3,X1)
% 1.81/0.98      | ~ r2_hidden(X2,X3)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_399,plain,
% 1.81/0.98      ( r1_orders_2(sK2,X0,X1)
% 1.81/0.98      | ~ r1_lattice3(sK2,X2,X0)
% 1.81/0.98      | ~ r2_hidden(X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_398]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2525,plain,
% 1.81/0.98      ( r1_orders_2(sK2,X0_45,X1_45)
% 1.81/0.98      | ~ r1_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | ~ r2_hidden(X1_45,X0_46)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_399]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2914,plain,
% 1.81/0.98      ( r1_orders_2(sK2,X0_45,X1_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) != iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2525]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3705,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,X0_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r2_hidden(X0_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2923,c_2914]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4222,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_46,X0_45),X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2915,c_3705]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4792,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_4226,c_4222]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4,plain,
% 1.81/0.98      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 1.81/0.98      | r1_lattice3(X0,X2,X1)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_449,plain,
% 1.81/0.98      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 1.81/0.98      | r1_lattice3(X0,X2,X1)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_450,plain,
% 1.81/0.98      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 1.81/0.98      | r1_lattice3(sK2,X1,X0)
% 1.81/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_449]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2522,plain,
% 1.81/0.98      ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45))
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_450]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2917,plain,
% 1.81/0.98      ( r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45)) != iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5650,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_4792,c_2917]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5655,plain,
% 1.81/0.98      ( r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,sK6) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5650,c_2923]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5656,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_5655]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_10,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_353,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_354,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0,X1)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.81/0.98      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_353]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2528,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.81/0.98      | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_354]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2911,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2528]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3871,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2911,c_2909]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_11,plain,
% 1.81/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.81/0.98      | r1_orders_2(X0,X3,X2)
% 1.81/0.98      | ~ r2_hidden(X3,X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_332,plain,
% 1.81/0.98      ( ~ r2_lattice3(X0,X1,X2)
% 1.81/0.98      | r1_orders_2(X0,X3,X2)
% 1.81/0.98      | ~ r2_hidden(X3,X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_333,plain,
% 1.81/0.98      ( ~ r2_lattice3(sK2,X0,X1)
% 1.81/0.98      | r1_orders_2(sK2,X2,X1)
% 1.81/0.98      | ~ r2_hidden(X2,X0)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_332]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2529,plain,
% 1.81/0.98      ( ~ r2_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | r1_orders_2(sK2,X1_45,X0_45)
% 1.81/0.98      | ~ r2_hidden(X1_45,X0_46)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.81/0.98      | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_333]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2910,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,X1_45,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2529]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3449,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,X0_45,sK6) = iProver_top
% 1.81/0.98      | r2_hidden(X0_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2923,c_2910]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3869,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2911,c_3449]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4691,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3871,c_3869]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_8,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_383,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_384,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0,X1)
% 1.81/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_383]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2526,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | ~ r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_384]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2913,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2526]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5499,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_4691,c_2913]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5504,plain,
% 1.81/0.98      ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | r2_lattice3(sK2,X0_46,sK6) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5499,c_2923]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5505,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_5504]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4224,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK0(sK2,X1_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,X1_46,X0_45),X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2915,c_3449]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4985,plain,
% 1.81/0.98      ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_4226,c_4224]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5,plain,
% 1.81/0.98      ( r1_lattice3(X0,X1,X2)
% 1.81/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_434,plain,
% 1.81/0.98      ( r1_lattice3(X0,X1,X2)
% 1.81/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_435,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0,X1)
% 1.81/0.98      | r2_hidden(sK0(sK2,X0,X1),X0)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_434]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2523,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_435]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2916,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2523]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4984,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2916,c_4224]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4791,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2916,c_4222]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_9,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | ~ l1_orders_2(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_368,plain,
% 1.81/0.98      ( r2_lattice3(X0,X1,X2)
% 1.81/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.81/0.98      | sK2 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_369,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0,X1)
% 1.81/0.98      | r2_hidden(sK1(sK2,X0,X1),X0)
% 1.81/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_368]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2527,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.81/0.98      | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46)
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_369]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2912,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2527]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4690,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2912,c_3869]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3867,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2911,c_3705]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4568,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3871,c_3867]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4567,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2912,c_3867]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4225,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK0(sK2,X1_46,X0_45)) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,X1_45,sK0(sK2,X1_46,X0_45)) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2915,c_2910]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4223,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),X1_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_45)) != iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2915,c_2914]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_0,plain,
% 1.81/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.81/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2538,plain,
% 1.81/0.98      ( ~ r2_hidden(X0_45,X0_46) | m1_subset_1(X0_45,X0_46) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2902,plain,
% 1.81/0.98      ( r2_hidden(X0_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,X0_46) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2538]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4047,plain,
% 1.81/0.98      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2916,c_2902]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_15,negated_conjecture,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 1.81/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2534,negated_conjecture,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2906,plain,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2534]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2930,plain,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2906,c_2533]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3546,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.81/0.98      | r2_hidden(sK6,X0_46) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2923,c_3449]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3574,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK6) = iProver_top
% 1.81/0.98      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2930,c_3546]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3738,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.81/0.98      | r2_hidden(sK6,X0_46) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2923,c_3705]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3757,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK6) != iProver_top
% 1.81/0.98      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_3738]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4037,plain,
% 1.81/0.98      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.81/0.98      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3574,c_3757]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3870,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r2_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
% 1.81/0.98      | r1_orders_2(sK2,X1_45,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2911,c_2910]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3868,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X1_45) = iProver_top
% 1.81/0.98      | r1_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X1_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2911,c_2914]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3283,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2912,c_2902]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3450,plain,
% 1.81/0.98      ( r2_lattice3(sK2,X0_46,sK1(sK2,u1_struct_0(sK2),X0_45)) != iProver_top
% 1.81/0.98      | r2_lattice3(sK2,u1_struct_0(sK2),X0_45) = iProver_top
% 1.81/0.98      | r1_orders_2(sK2,X1_45,sK1(sK2,u1_struct_0(sK2),X0_45)) = iProver_top
% 1.81/0.98      | r2_hidden(X1_45,X0_46) != iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.81/0.98      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3283,c_2910]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3243,plain,
% 1.81/0.98      ( r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2923,c_2909]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_14,negated_conjecture,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.81/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2535,negated_conjecture,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2905,plain,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 1.81/0.98      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2535]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2940,plain,
% 1.81/0.98      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 1.81/0.98      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2905,c_2533]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_13,negated_conjecture,
% 1.81/0.98      ( ~ r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5) ),
% 1.81/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2536,negated_conjecture,
% 1.81/0.98      ( ~ r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2904,plain,
% 1.81/0.98      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2536]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2935,plain,
% 1.81/0.98      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.81/0.98      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2904,c_2533]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_19,negated_conjecture,
% 1.81/0.98      ( ~ v2_struct_0(sK3) ),
% 1.81/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_272,plain,
% 1.81/0.98      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_232,c_19]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_273,plain,
% 1.81/0.98      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_272]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_298,plain,
% 1.81/0.98      ( r2_hidden(X0,X1)
% 1.81/0.98      | ~ m1_subset_1(X0,X1)
% 1.81/0.98      | ~ l1_orders_2(sK3)
% 1.81/0.98      | u1_struct_0(sK3) != X1 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_273]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_299,plain,
% 1.81/0.98      ( r2_hidden(X0,u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/0.98      | ~ l1_orders_2(sK3) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_298]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_464,plain,
% 1.81/0.98      ( r2_hidden(X0,u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.81/0.98      | sK2 != sK3 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_299]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2521,plain,
% 1.81/0.98      ( r2_hidden(X0_45,u1_struct_0(sK3))
% 1.81/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
% 1.81/0.98      | sK2 != sK3 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_464]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2918,plain,
% 1.81/0.98      ( sK2 != sK3
% 1.81/0.98      | r2_hidden(X0_45,u1_struct_0(sK3)) = iProver_top
% 1.81/0.98      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2521]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_12,negated_conjecture,
% 1.81/0.98      ( ~ r2_lattice3(sK3,sK4,sK6) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.81/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2537,negated_conjecture,
% 1.81/0.98      ( ~ r2_lattice3(sK3,sK4,sK6) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2903,plain,
% 1.81/0.98      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.81/0.98      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2537]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_17,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2532,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2907,plain,
% 1.81/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2532]) ).
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  % SZS output end Saturation for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  ------                               Statistics
% 1.81/0.98  
% 1.81/0.98  ------ General
% 1.81/0.98  
% 1.81/0.98  abstr_ref_over_cycles:                  0
% 1.81/0.98  abstr_ref_under_cycles:                 0
% 1.81/0.98  gc_basic_clause_elim:                   0
% 1.81/0.98  forced_gc_time:                         0
% 1.81/0.98  parsing_time:                           0.01
% 1.81/0.98  unif_index_cands_time:                  0.
% 1.81/0.98  unif_index_add_time:                    0.
% 1.81/0.98  orderings_time:                         0.
% 1.81/0.98  out_proof_time:                         0.
% 1.81/0.98  total_time:                             0.216
% 1.81/0.98  num_of_symbols:                         48
% 1.81/0.98  num_of_terms:                           3254
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing
% 1.81/0.98  
% 1.81/0.98  num_of_splits:                          0
% 1.81/0.98  num_of_split_atoms:                     0
% 1.81/0.98  num_of_reused_defs:                     0
% 1.81/0.98  num_eq_ax_congr_red:                    17
% 1.81/0.98  num_of_sem_filtered_clauses:            1
% 1.81/0.98  num_of_subtypes:                        3
% 1.81/0.98  monotx_restored_types:                  0
% 1.81/0.98  sat_num_of_epr_types:                   0
% 1.81/0.98  sat_num_of_non_cyclic_types:            0
% 1.81/0.98  sat_guarded_non_collapsed_types:        0
% 1.81/0.98  num_pure_diseq_elim:                    0
% 1.81/0.98  simp_replaced_by:                       0
% 1.81/0.98  res_preprocessed:                       103
% 1.81/0.98  prep_upred:                             0
% 1.81/0.98  prep_unflattend:                        153
% 1.81/0.98  smt_new_axioms:                         0
% 1.81/0.98  pred_elim_cands:                        5
% 1.81/0.98  pred_elim:                              4
% 1.81/0.98  pred_elim_cl:                           4
% 1.81/0.98  pred_elim_cycles:                       13
% 1.81/0.98  merged_defs:                            0
% 1.81/0.98  merged_defs_ncl:                        0
% 1.81/0.98  bin_hyper_res:                          0
% 1.81/0.98  prep_cycles:                            4
% 1.81/0.98  pred_elim_time:                         0.034
% 1.81/0.98  splitting_time:                         0.
% 1.81/0.98  sem_filter_time:                        0.
% 1.81/0.98  monotx_time:                            0.
% 1.81/0.98  subtype_inf_time:                       0.
% 1.81/0.98  
% 1.81/0.98  ------ Problem properties
% 1.81/0.98  
% 1.81/0.98  clauses:                                18
% 1.81/0.98  conjectures:                            7
% 1.81/0.98  epr:                                    6
% 1.81/0.98  horn:                                   13
% 1.81/0.98  ground:                                 7
% 1.81/0.98  unary:                                  3
% 1.81/0.98  binary:                                 6
% 1.81/0.98  lits:                                   46
% 1.81/0.98  lits_eq:                                2
% 1.81/0.98  fd_pure:                                0
% 1.81/0.98  fd_pseudo:                              0
% 1.81/0.98  fd_cond:                                0
% 1.81/0.98  fd_pseudo_cond:                         0
% 1.81/0.98  ac_symbols:                             0
% 1.81/0.98  
% 1.81/0.98  ------ Propositional Solver
% 1.81/0.98  
% 1.81/0.98  prop_solver_calls:                      27
% 1.81/0.98  prop_fast_solver_calls:                 1339
% 1.81/0.98  smt_solver_calls:                       0
% 1.81/0.98  smt_fast_solver_calls:                  0
% 1.81/0.98  prop_num_of_clauses:                    1103
% 1.81/0.98  prop_preprocess_simplified:             4485
% 1.81/0.98  prop_fo_subsumed:                       46
% 1.81/0.98  prop_solver_time:                       0.
% 1.81/0.98  smt_solver_time:                        0.
% 1.81/0.98  smt_fast_solver_time:                   0.
% 1.81/0.98  prop_fast_solver_time:                  0.
% 1.81/0.98  prop_unsat_core_time:                   0.
% 1.81/0.98  
% 1.81/0.98  ------ QBF
% 1.81/0.98  
% 1.81/0.98  qbf_q_res:                              0
% 1.81/0.98  qbf_num_tautologies:                    0
% 1.81/0.98  qbf_prep_cycles:                        0
% 1.81/0.98  
% 1.81/0.98  ------ BMC1
% 1.81/0.98  
% 1.81/0.98  bmc1_current_bound:                     -1
% 1.81/0.98  bmc1_last_solved_bound:                 -1
% 1.81/0.98  bmc1_unsat_core_size:                   -1
% 1.81/0.98  bmc1_unsat_core_parents_size:           -1
% 1.81/0.98  bmc1_merge_next_fun:                    0
% 1.81/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation
% 1.81/0.98  
% 1.81/0.98  inst_num_of_clauses:                    266
% 1.81/0.98  inst_num_in_passive:                    37
% 1.81/0.98  inst_num_in_active:                     223
% 1.81/0.98  inst_num_in_unprocessed:                6
% 1.81/0.98  inst_num_of_loops:                      240
% 1.81/0.98  inst_num_of_learning_restarts:          0
% 1.81/0.98  inst_num_moves_active_passive:          13
% 1.81/0.98  inst_lit_activity:                      0
% 1.81/0.98  inst_lit_activity_moves:                0
% 1.81/0.98  inst_num_tautologies:                   0
% 1.81/0.98  inst_num_prop_implied:                  0
% 1.81/0.98  inst_num_existing_simplified:           0
% 1.81/0.98  inst_num_eq_res_simplified:             0
% 1.81/0.98  inst_num_child_elim:                    0
% 1.81/0.98  inst_num_of_dismatching_blockings:      225
% 1.81/0.98  inst_num_of_non_proper_insts:           603
% 1.81/0.98  inst_num_of_duplicates:                 0
% 1.81/0.98  inst_inst_num_from_inst_to_res:         0
% 1.81/0.98  inst_dismatching_checking_time:         0.
% 1.81/0.98  
% 1.81/0.98  ------ Resolution
% 1.81/0.98  
% 1.81/0.98  res_num_of_clauses:                     0
% 1.81/0.98  res_num_in_passive:                     0
% 1.81/0.98  res_num_in_active:                      0
% 1.81/0.98  res_num_of_loops:                       107
% 1.81/0.98  res_forward_subset_subsumed:            23
% 1.81/0.98  res_backward_subset_subsumed:           0
% 1.81/0.98  res_forward_subsumed:                   8
% 1.81/0.98  res_backward_subsumed:                  0
% 1.81/0.98  res_forward_subsumption_resolution:     6
% 1.81/0.98  res_backward_subsumption_resolution:    0
% 1.81/0.98  res_clause_to_clause_subsumption:       401
% 1.81/0.98  res_orphan_elimination:                 0
% 1.81/0.98  res_tautology_del:                      95
% 1.81/0.98  res_num_eq_res_simplified:              0
% 1.81/0.98  res_num_sel_changes:                    0
% 1.81/0.98  res_moves_from_active_to_pass:          0
% 1.81/0.98  
% 1.81/0.98  ------ Superposition
% 1.81/0.98  
% 1.81/0.98  sup_time_total:                         0.
% 1.81/0.98  sup_time_generating:                    0.
% 1.81/0.98  sup_time_sim_full:                      0.
% 1.81/0.98  sup_time_sim_immed:                     0.
% 1.81/0.98  
% 1.81/0.98  sup_num_of_clauses:                     56
% 1.81/0.98  sup_num_in_active:                      47
% 1.81/0.98  sup_num_in_passive:                     9
% 1.81/0.98  sup_num_of_loops:                       47
% 1.81/0.98  sup_fw_superposition:                   18
% 1.81/0.98  sup_bw_superposition:                   25
% 1.81/0.98  sup_immediate_simplified:               2
% 1.81/0.98  sup_given_eliminated:                   0
% 1.81/0.98  comparisons_done:                       0
% 1.81/0.98  comparisons_avoided:                    0
% 1.81/0.98  
% 1.81/0.98  ------ Simplifications
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  sim_fw_subset_subsumed:                 0
% 1.81/0.98  sim_bw_subset_subsumed:                 0
% 1.81/0.98  sim_fw_subsumed:                        9
% 1.81/0.98  sim_bw_subsumed:                        0
% 1.81/0.98  sim_fw_subsumption_res:                 0
% 1.81/0.98  sim_bw_subsumption_res:                 0
% 1.81/0.98  sim_tautology_del:                      2
% 1.81/0.98  sim_eq_tautology_del:                   0
% 1.81/0.98  sim_eq_res_simp:                        0
% 1.81/0.98  sim_fw_demodulated:                     0
% 1.81/0.98  sim_bw_demodulated:                     0
% 1.81/0.98  sim_light_normalised:                   4
% 1.81/0.98  sim_joinable_taut:                      0
% 1.81/0.98  sim_joinable_simp:                      0
% 1.81/0.98  sim_ac_normalised:                      0
% 1.81/0.98  sim_smt_subsumption:                    0
% 1.81/0.98  
%------------------------------------------------------------------------------
