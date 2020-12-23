%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:00 EST 2020

% Result     : CounterSatisfiable 1.39s
% Output     : Saturation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  175 (1844 expanded)
%              Number of clauses        :  121 ( 458 expanded)
%              Number of leaves         :   16 ( 524 expanded)
%              Depth                    :   20
%              Number of atoms          :  699 (15446 expanded)
%              Number of equality atoms :  205 (1769 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f9,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f32,f31,f30,f29])).

fof(f46,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_196,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_195,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_192,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2443,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_407,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_408,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_2429,plain,
    ( r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_2800,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_220,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_270,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_220,c_20])).

cnf(c_271,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_273,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_19])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_273])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_2435,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | r2_hidden(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_2794,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_45,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_3633,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2794])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2436,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2793,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_15,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2438,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2808,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2793,c_2438])).

cnf(c_6,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_386,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_387,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_2430,plain,
    ( r1_orders_2(sK2,X0_45,X1_45)
    | ~ r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | ~ r2_hidden(X1_45,X0_46) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_2799,plain,
    ( r1_orders_2(sK2,X0_45,X1_45) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2430])).

cnf(c_3528,plain,
    ( r1_orders_2(sK2,sK6,X0_45) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_45,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_2799])).

cnf(c_3629,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_3528])).

cnf(c_4024,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_3629])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_437,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_438,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_2427,plain,
    ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45))
    | r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_2802,plain,
    ( r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45)) != iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2427])).

cnf(c_4893,plain,
    ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_2802])).

cnf(c_4898,plain,
    ( r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_lattice3(sK2,X0_46,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_2808])).

cnf(c_4899,plain,
    ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4898])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_341,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_342,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_2433,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_342])).

cnf(c_2796,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_3240,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_2794])).

cnf(c_10,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_320,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_321,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_2434,plain,
    ( ~ r2_lattice3(sK2,X0_46,X0_45)
    | r1_orders_2(sK2,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | ~ r2_hidden(X1_45,X0_46) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_2795,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) != iProver_top
    | r1_orders_2(sK2,X1_45,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2434])).

cnf(c_3312,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,X0_45,sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_45,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_2795])).

cnf(c_3402,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X1_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_3312])).

cnf(c_3997,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_3402])).

cnf(c_7,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_371,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_372,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_2431,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_2798,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2431])).

cnf(c_4531,plain,
    ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3997,c_2798])).

cnf(c_4619,plain,
    ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r2_lattice3(sK2,X0_46,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4531,c_2808])).

cnf(c_4620,plain,
    ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
    | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4619])).

cnf(c_3631,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X1_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X1_46,X0_45),X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_3312])).

cnf(c_4213,plain,
    ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_3631])).

cnf(c_4,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_422,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_19])).

cnf(c_423,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_2428,plain,
    ( r1_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_2801,plain,
    ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_4212,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_3631])).

cnf(c_3562,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X1_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_3528])).

cnf(c_3996,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_3562])).

cnf(c_3900,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2801,c_3629])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_356,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_357,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(sK1(sK2,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_2432,plain,
    ( r2_lattice3(sK2,X0_46,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) ),
    inference(subtyping,[status(esa)],[c_357])).

cnf(c_2797,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_3890,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_3562])).

cnf(c_3789,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2797,c_3402])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2439,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2791,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2811,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2791,c_2438])).

cnf(c_3401,plain,
    ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
    | r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r2_hidden(sK6,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3312])).

cnf(c_3429,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_3401])).

cnf(c_3561,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,X0_46,sK6) != iProver_top
    | r2_hidden(sK6,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_3528])).

cnf(c_3580,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) != iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3561])).

cnf(c_3777,plain,
    ( r1_orders_2(sK2,sK6,sK6) = iProver_top
    | r2_hidden(sK6,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3429,c_3580])).

cnf(c_3632,plain,
    ( r2_lattice3(sK2,X0_46,sK0(sK2,X1_46,X0_45)) != iProver_top
    | r1_orders_2(sK2,X1_45,sK0(sK2,X1_46,X0_45)) = iProver_top
    | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2795])).

cnf(c_3630,plain,
    ( r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),X1_45) = iProver_top
    | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_45)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2799])).

cnf(c_3529,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X1_45) = iProver_top
    | r1_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_2799])).

cnf(c_3313,plain,
    ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
    | r2_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
    | r1_orders_2(sK2,X1_45,sK1(sK2,X0_46,X0_45)) = iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1_45,X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_2795])).

cnf(c_3123,plain,
    ( r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_2794])).

cnf(c_13,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2440,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2790,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_2821,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2790,c_2438])).

cnf(c_12,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2441,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2789,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_2816,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2789,c_2438])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_260,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_220,c_18])).

cnf(c_261,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | ~ l1_orders_2(sK3)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_261])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,u1_struct_0(sK3))
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_287])).

cnf(c_2426,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | r2_hidden(X0_45,u1_struct_0(sK3))
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_2803,plain,
    ( sK2 != sK3
    | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_45,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2426])).

cnf(c_11,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2442,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2788,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2442])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2437,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2792,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:00:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.39/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.39/0.99  
% 1.39/0.99  ------  iProver source info
% 1.39/0.99  
% 1.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.39/0.99  git: non_committed_changes: false
% 1.39/0.99  git: last_make_outside_of_git: false
% 1.39/0.99  
% 1.39/0.99  ------ 
% 1.39/0.99  
% 1.39/0.99  ------ Input Options
% 1.39/0.99  
% 1.39/0.99  --out_options                           all
% 1.39/0.99  --tptp_safe_out                         true
% 1.39/0.99  --problem_path                          ""
% 1.39/0.99  --include_path                          ""
% 1.39/0.99  --clausifier                            res/vclausify_rel
% 1.39/0.99  --clausifier_options                    --mode clausify
% 1.39/0.99  --stdin                                 false
% 1.39/0.99  --stats_out                             all
% 1.39/0.99  
% 1.39/0.99  ------ General Options
% 1.39/0.99  
% 1.39/0.99  --fof                                   false
% 1.39/0.99  --time_out_real                         305.
% 1.39/0.99  --time_out_virtual                      -1.
% 1.39/0.99  --symbol_type_check                     false
% 1.39/0.99  --clausify_out                          false
% 1.39/0.99  --sig_cnt_out                           false
% 1.39/0.99  --trig_cnt_out                          false
% 1.39/0.99  --trig_cnt_out_tolerance                1.
% 1.39/0.99  --trig_cnt_out_sk_spl                   false
% 1.39/0.99  --abstr_cl_out                          false
% 1.39/0.99  
% 1.39/0.99  ------ Global Options
% 1.39/0.99  
% 1.39/0.99  --schedule                              default
% 1.39/0.99  --add_important_lit                     false
% 1.39/0.99  --prop_solver_per_cl                    1000
% 1.39/0.99  --min_unsat_core                        false
% 1.39/0.99  --soft_assumptions                      false
% 1.39/0.99  --soft_lemma_size                       3
% 1.39/0.99  --prop_impl_unit_size                   0
% 1.39/0.99  --prop_impl_unit                        []
% 1.39/0.99  --share_sel_clauses                     true
% 1.39/0.99  --reset_solvers                         false
% 1.39/0.99  --bc_imp_inh                            [conj_cone]
% 1.39/0.99  --conj_cone_tolerance                   3.
% 1.39/0.99  --extra_neg_conj                        none
% 1.39/0.99  --large_theory_mode                     true
% 1.39/0.99  --prolific_symb_bound                   200
% 1.39/0.99  --lt_threshold                          2000
% 1.39/0.99  --clause_weak_htbl                      true
% 1.39/0.99  --gc_record_bc_elim                     false
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing Options
% 1.39/0.99  
% 1.39/0.99  --preprocessing_flag                    true
% 1.39/0.99  --time_out_prep_mult                    0.1
% 1.39/0.99  --splitting_mode                        input
% 1.39/0.99  --splitting_grd                         true
% 1.39/0.99  --splitting_cvd                         false
% 1.39/0.99  --splitting_cvd_svl                     false
% 1.39/0.99  --splitting_nvd                         32
% 1.39/0.99  --sub_typing                            true
% 1.39/0.99  --prep_gs_sim                           true
% 1.39/0.99  --prep_unflatten                        true
% 1.39/0.99  --prep_res_sim                          true
% 1.39/0.99  --prep_upred                            true
% 1.39/0.99  --prep_sem_filter                       exhaustive
% 1.39/0.99  --prep_sem_filter_out                   false
% 1.39/0.99  --pred_elim                             true
% 1.39/0.99  --res_sim_input                         true
% 1.39/0.99  --eq_ax_congr_red                       true
% 1.39/0.99  --pure_diseq_elim                       true
% 1.39/0.99  --brand_transform                       false
% 1.39/0.99  --non_eq_to_eq                          false
% 1.39/0.99  --prep_def_merge                        true
% 1.39/0.99  --prep_def_merge_prop_impl              false
% 1.39/0.99  --prep_def_merge_mbd                    true
% 1.39/0.99  --prep_def_merge_tr_red                 false
% 1.39/0.99  --prep_def_merge_tr_cl                  false
% 1.39/0.99  --smt_preprocessing                     true
% 1.39/0.99  --smt_ac_axioms                         fast
% 1.39/0.99  --preprocessed_out                      false
% 1.39/0.99  --preprocessed_stats                    false
% 1.39/0.99  
% 1.39/0.99  ------ Abstraction refinement Options
% 1.39/0.99  
% 1.39/0.99  --abstr_ref                             []
% 1.39/0.99  --abstr_ref_prep                        false
% 1.39/0.99  --abstr_ref_until_sat                   false
% 1.39/0.99  --abstr_ref_sig_restrict                funpre
% 1.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/0.99  --abstr_ref_under                       []
% 1.39/0.99  
% 1.39/0.99  ------ SAT Options
% 1.39/0.99  
% 1.39/0.99  --sat_mode                              false
% 1.39/0.99  --sat_fm_restart_options                ""
% 1.39/0.99  --sat_gr_def                            false
% 1.39/0.99  --sat_epr_types                         true
% 1.39/0.99  --sat_non_cyclic_types                  false
% 1.39/0.99  --sat_finite_models                     false
% 1.39/0.99  --sat_fm_lemmas                         false
% 1.39/0.99  --sat_fm_prep                           false
% 1.39/0.99  --sat_fm_uc_incr                        true
% 1.39/0.99  --sat_out_model                         small
% 1.39/0.99  --sat_out_clauses                       false
% 1.39/0.99  
% 1.39/0.99  ------ QBF Options
% 1.39/0.99  
% 1.39/0.99  --qbf_mode                              false
% 1.39/0.99  --qbf_elim_univ                         false
% 1.39/0.99  --qbf_dom_inst                          none
% 1.39/0.99  --qbf_dom_pre_inst                      false
% 1.39/0.99  --qbf_sk_in                             false
% 1.39/0.99  --qbf_pred_elim                         true
% 1.39/0.99  --qbf_split                             512
% 1.39/0.99  
% 1.39/0.99  ------ BMC1 Options
% 1.39/0.99  
% 1.39/0.99  --bmc1_incremental                      false
% 1.39/0.99  --bmc1_axioms                           reachable_all
% 1.39/0.99  --bmc1_min_bound                        0
% 1.39/0.99  --bmc1_max_bound                        -1
% 1.39/0.99  --bmc1_max_bound_default                -1
% 1.39/0.99  --bmc1_symbol_reachability              true
% 1.39/0.99  --bmc1_property_lemmas                  false
% 1.39/0.99  --bmc1_k_induction                      false
% 1.39/0.99  --bmc1_non_equiv_states                 false
% 1.39/0.99  --bmc1_deadlock                         false
% 1.39/0.99  --bmc1_ucm                              false
% 1.39/0.99  --bmc1_add_unsat_core                   none
% 1.39/0.99  --bmc1_unsat_core_children              false
% 1.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/0.99  --bmc1_out_stat                         full
% 1.39/0.99  --bmc1_ground_init                      false
% 1.39/0.99  --bmc1_pre_inst_next_state              false
% 1.39/0.99  --bmc1_pre_inst_state                   false
% 1.39/0.99  --bmc1_pre_inst_reach_state             false
% 1.39/0.99  --bmc1_out_unsat_core                   false
% 1.39/0.99  --bmc1_aig_witness_out                  false
% 1.39/0.99  --bmc1_verbose                          false
% 1.39/0.99  --bmc1_dump_clauses_tptp                false
% 1.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.39/0.99  --bmc1_dump_file                        -
% 1.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.39/0.99  --bmc1_ucm_extend_mode                  1
% 1.39/0.99  --bmc1_ucm_init_mode                    2
% 1.39/0.99  --bmc1_ucm_cone_mode                    none
% 1.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.39/0.99  --bmc1_ucm_relax_model                  4
% 1.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/0.99  --bmc1_ucm_layered_model                none
% 1.39/0.99  --bmc1_ucm_max_lemma_size               10
% 1.39/0.99  
% 1.39/0.99  ------ AIG Options
% 1.39/0.99  
% 1.39/0.99  --aig_mode                              false
% 1.39/0.99  
% 1.39/0.99  ------ Instantiation Options
% 1.39/0.99  
% 1.39/0.99  --instantiation_flag                    true
% 1.39/0.99  --inst_sos_flag                         false
% 1.39/0.99  --inst_sos_phase                        true
% 1.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/0.99  --inst_lit_sel_side                     num_symb
% 1.39/0.99  --inst_solver_per_active                1400
% 1.39/0.99  --inst_solver_calls_frac                1.
% 1.39/0.99  --inst_passive_queue_type               priority_queues
% 1.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/0.99  --inst_passive_queues_freq              [25;2]
% 1.39/0.99  --inst_dismatching                      true
% 1.39/0.99  --inst_eager_unprocessed_to_passive     true
% 1.39/0.99  --inst_prop_sim_given                   true
% 1.39/0.99  --inst_prop_sim_new                     false
% 1.39/0.99  --inst_subs_new                         false
% 1.39/0.99  --inst_eq_res_simp                      false
% 1.39/0.99  --inst_subs_given                       false
% 1.39/0.99  --inst_orphan_elimination               true
% 1.39/0.99  --inst_learning_loop_flag               true
% 1.39/0.99  --inst_learning_start                   3000
% 1.39/0.99  --inst_learning_factor                  2
% 1.39/0.99  --inst_start_prop_sim_after_learn       3
% 1.39/0.99  --inst_sel_renew                        solver
% 1.39/0.99  --inst_lit_activity_flag                true
% 1.39/0.99  --inst_restr_to_given                   false
% 1.39/0.99  --inst_activity_threshold               500
% 1.39/0.99  --inst_out_proof                        true
% 1.39/0.99  
% 1.39/0.99  ------ Resolution Options
% 1.39/0.99  
% 1.39/0.99  --resolution_flag                       true
% 1.39/0.99  --res_lit_sel                           adaptive
% 1.39/0.99  --res_lit_sel_side                      none
% 1.39/0.99  --res_ordering                          kbo
% 1.39/0.99  --res_to_prop_solver                    active
% 1.39/0.99  --res_prop_simpl_new                    false
% 1.39/0.99  --res_prop_simpl_given                  true
% 1.39/0.99  --res_passive_queue_type                priority_queues
% 1.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/0.99  --res_passive_queues_freq               [15;5]
% 1.39/0.99  --res_forward_subs                      full
% 1.39/0.99  --res_backward_subs                     full
% 1.39/0.99  --res_forward_subs_resolution           true
% 1.39/0.99  --res_backward_subs_resolution          true
% 1.39/0.99  --res_orphan_elimination                true
% 1.39/0.99  --res_time_limit                        2.
% 1.39/0.99  --res_out_proof                         true
% 1.39/0.99  
% 1.39/0.99  ------ Superposition Options
% 1.39/0.99  
% 1.39/0.99  --superposition_flag                    true
% 1.39/0.99  --sup_passive_queue_type                priority_queues
% 1.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.39/0.99  --demod_completeness_check              fast
% 1.39/0.99  --demod_use_ground                      true
% 1.39/0.99  --sup_to_prop_solver                    passive
% 1.39/0.99  --sup_prop_simpl_new                    true
% 1.39/0.99  --sup_prop_simpl_given                  true
% 1.39/0.99  --sup_fun_splitting                     false
% 1.39/0.99  --sup_smt_interval                      50000
% 1.39/0.99  
% 1.39/0.99  ------ Superposition Simplification Setup
% 1.39/0.99  
% 1.39/0.99  --sup_indices_passive                   []
% 1.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_full_bw                           [BwDemod]
% 1.39/0.99  --sup_immed_triv                        [TrivRules]
% 1.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_immed_bw_main                     []
% 1.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/0.99  
% 1.39/0.99  ------ Combination Options
% 1.39/0.99  
% 1.39/0.99  --comb_res_mult                         3
% 1.39/0.99  --comb_sup_mult                         2
% 1.39/0.99  --comb_inst_mult                        10
% 1.39/0.99  
% 1.39/0.99  ------ Debug Options
% 1.39/0.99  
% 1.39/0.99  --dbg_backtrace                         false
% 1.39/0.99  --dbg_dump_prop_clauses                 false
% 1.39/0.99  --dbg_dump_prop_clauses_file            -
% 1.39/0.99  --dbg_out_stat                          false
% 1.39/0.99  ------ Parsing...
% 1.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.39/0.99  ------ Proving...
% 1.39/0.99  ------ Problem Properties 
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  clauses                                 17
% 1.39/0.99  conjectures                             7
% 1.39/0.99  EPR                                     5
% 1.39/0.99  Horn                                    12
% 1.39/0.99  unary                                   3
% 1.39/0.99  binary                                  5
% 1.39/0.99  lits                                    44
% 1.39/0.99  lits eq                                 2
% 1.39/0.99  fd_pure                                 0
% 1.39/0.99  fd_pseudo                               0
% 1.39/0.99  fd_cond                                 0
% 1.39/0.99  fd_pseudo_cond                          0
% 1.39/0.99  AC symbols                              0
% 1.39/0.99  
% 1.39/0.99  ------ Schedule dynamic 5 is on 
% 1.39/0.99  
% 1.39/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  ------ 
% 1.39/0.99  Current options:
% 1.39/0.99  ------ 
% 1.39/0.99  
% 1.39/0.99  ------ Input Options
% 1.39/0.99  
% 1.39/0.99  --out_options                           all
% 1.39/0.99  --tptp_safe_out                         true
% 1.39/0.99  --problem_path                          ""
% 1.39/0.99  --include_path                          ""
% 1.39/0.99  --clausifier                            res/vclausify_rel
% 1.39/0.99  --clausifier_options                    --mode clausify
% 1.39/0.99  --stdin                                 false
% 1.39/0.99  --stats_out                             all
% 1.39/0.99  
% 1.39/0.99  ------ General Options
% 1.39/0.99  
% 1.39/0.99  --fof                                   false
% 1.39/0.99  --time_out_real                         305.
% 1.39/0.99  --time_out_virtual                      -1.
% 1.39/0.99  --symbol_type_check                     false
% 1.39/0.99  --clausify_out                          false
% 1.39/0.99  --sig_cnt_out                           false
% 1.39/0.99  --trig_cnt_out                          false
% 1.39/0.99  --trig_cnt_out_tolerance                1.
% 1.39/0.99  --trig_cnt_out_sk_spl                   false
% 1.39/0.99  --abstr_cl_out                          false
% 1.39/0.99  
% 1.39/0.99  ------ Global Options
% 1.39/0.99  
% 1.39/0.99  --schedule                              default
% 1.39/0.99  --add_important_lit                     false
% 1.39/0.99  --prop_solver_per_cl                    1000
% 1.39/0.99  --min_unsat_core                        false
% 1.39/0.99  --soft_assumptions                      false
% 1.39/0.99  --soft_lemma_size                       3
% 1.39/0.99  --prop_impl_unit_size                   0
% 1.39/0.99  --prop_impl_unit                        []
% 1.39/0.99  --share_sel_clauses                     true
% 1.39/0.99  --reset_solvers                         false
% 1.39/0.99  --bc_imp_inh                            [conj_cone]
% 1.39/0.99  --conj_cone_tolerance                   3.
% 1.39/0.99  --extra_neg_conj                        none
% 1.39/0.99  --large_theory_mode                     true
% 1.39/0.99  --prolific_symb_bound                   200
% 1.39/0.99  --lt_threshold                          2000
% 1.39/0.99  --clause_weak_htbl                      true
% 1.39/0.99  --gc_record_bc_elim                     false
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing Options
% 1.39/0.99  
% 1.39/0.99  --preprocessing_flag                    true
% 1.39/0.99  --time_out_prep_mult                    0.1
% 1.39/0.99  --splitting_mode                        input
% 1.39/0.99  --splitting_grd                         true
% 1.39/0.99  --splitting_cvd                         false
% 1.39/0.99  --splitting_cvd_svl                     false
% 1.39/0.99  --splitting_nvd                         32
% 1.39/0.99  --sub_typing                            true
% 1.39/0.99  --prep_gs_sim                           true
% 1.39/0.99  --prep_unflatten                        true
% 1.39/0.99  --prep_res_sim                          true
% 1.39/0.99  --prep_upred                            true
% 1.39/0.99  --prep_sem_filter                       exhaustive
% 1.39/0.99  --prep_sem_filter_out                   false
% 1.39/0.99  --pred_elim                             true
% 1.39/0.99  --res_sim_input                         true
% 1.39/0.99  --eq_ax_congr_red                       true
% 1.39/0.99  --pure_diseq_elim                       true
% 1.39/0.99  --brand_transform                       false
% 1.39/0.99  --non_eq_to_eq                          false
% 1.39/0.99  --prep_def_merge                        true
% 1.39/0.99  --prep_def_merge_prop_impl              false
% 1.39/0.99  --prep_def_merge_mbd                    true
% 1.39/0.99  --prep_def_merge_tr_red                 false
% 1.39/0.99  --prep_def_merge_tr_cl                  false
% 1.39/0.99  --smt_preprocessing                     true
% 1.39/0.99  --smt_ac_axioms                         fast
% 1.39/0.99  --preprocessed_out                      false
% 1.39/0.99  --preprocessed_stats                    false
% 1.39/0.99  
% 1.39/0.99  ------ Abstraction refinement Options
% 1.39/0.99  
% 1.39/0.99  --abstr_ref                             []
% 1.39/0.99  --abstr_ref_prep                        false
% 1.39/0.99  --abstr_ref_until_sat                   false
% 1.39/0.99  --abstr_ref_sig_restrict                funpre
% 1.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/0.99  --abstr_ref_under                       []
% 1.39/0.99  
% 1.39/0.99  ------ SAT Options
% 1.39/0.99  
% 1.39/0.99  --sat_mode                              false
% 1.39/0.99  --sat_fm_restart_options                ""
% 1.39/0.99  --sat_gr_def                            false
% 1.39/0.99  --sat_epr_types                         true
% 1.39/0.99  --sat_non_cyclic_types                  false
% 1.39/0.99  --sat_finite_models                     false
% 1.39/0.99  --sat_fm_lemmas                         false
% 1.39/0.99  --sat_fm_prep                           false
% 1.39/0.99  --sat_fm_uc_incr                        true
% 1.39/0.99  --sat_out_model                         small
% 1.39/0.99  --sat_out_clauses                       false
% 1.39/0.99  
% 1.39/0.99  ------ QBF Options
% 1.39/0.99  
% 1.39/0.99  --qbf_mode                              false
% 1.39/0.99  --qbf_elim_univ                         false
% 1.39/0.99  --qbf_dom_inst                          none
% 1.39/0.99  --qbf_dom_pre_inst                      false
% 1.39/0.99  --qbf_sk_in                             false
% 1.39/0.99  --qbf_pred_elim                         true
% 1.39/0.99  --qbf_split                             512
% 1.39/0.99  
% 1.39/0.99  ------ BMC1 Options
% 1.39/0.99  
% 1.39/0.99  --bmc1_incremental                      false
% 1.39/0.99  --bmc1_axioms                           reachable_all
% 1.39/0.99  --bmc1_min_bound                        0
% 1.39/0.99  --bmc1_max_bound                        -1
% 1.39/0.99  --bmc1_max_bound_default                -1
% 1.39/0.99  --bmc1_symbol_reachability              true
% 1.39/0.99  --bmc1_property_lemmas                  false
% 1.39/0.99  --bmc1_k_induction                      false
% 1.39/0.99  --bmc1_non_equiv_states                 false
% 1.39/0.99  --bmc1_deadlock                         false
% 1.39/0.99  --bmc1_ucm                              false
% 1.39/0.99  --bmc1_add_unsat_core                   none
% 1.39/0.99  --bmc1_unsat_core_children              false
% 1.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/0.99  --bmc1_out_stat                         full
% 1.39/0.99  --bmc1_ground_init                      false
% 1.39/0.99  --bmc1_pre_inst_next_state              false
% 1.39/0.99  --bmc1_pre_inst_state                   false
% 1.39/0.99  --bmc1_pre_inst_reach_state             false
% 1.39/0.99  --bmc1_out_unsat_core                   false
% 1.39/0.99  --bmc1_aig_witness_out                  false
% 1.39/0.99  --bmc1_verbose                          false
% 1.39/0.99  --bmc1_dump_clauses_tptp                false
% 1.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.39/0.99  --bmc1_dump_file                        -
% 1.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.39/0.99  --bmc1_ucm_extend_mode                  1
% 1.39/0.99  --bmc1_ucm_init_mode                    2
% 1.39/0.99  --bmc1_ucm_cone_mode                    none
% 1.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.39/0.99  --bmc1_ucm_relax_model                  4
% 1.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/0.99  --bmc1_ucm_layered_model                none
% 1.39/0.99  --bmc1_ucm_max_lemma_size               10
% 1.39/0.99  
% 1.39/0.99  ------ AIG Options
% 1.39/0.99  
% 1.39/0.99  --aig_mode                              false
% 1.39/0.99  
% 1.39/0.99  ------ Instantiation Options
% 1.39/0.99  
% 1.39/0.99  --instantiation_flag                    true
% 1.39/0.99  --inst_sos_flag                         false
% 1.39/0.99  --inst_sos_phase                        true
% 1.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/0.99  --inst_lit_sel_side                     none
% 1.39/0.99  --inst_solver_per_active                1400
% 1.39/0.99  --inst_solver_calls_frac                1.
% 1.39/0.99  --inst_passive_queue_type               priority_queues
% 1.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/0.99  --inst_passive_queues_freq              [25;2]
% 1.39/0.99  --inst_dismatching                      true
% 1.39/0.99  --inst_eager_unprocessed_to_passive     true
% 1.39/0.99  --inst_prop_sim_given                   true
% 1.39/0.99  --inst_prop_sim_new                     false
% 1.39/0.99  --inst_subs_new                         false
% 1.39/0.99  --inst_eq_res_simp                      false
% 1.39/0.99  --inst_subs_given                       false
% 1.39/0.99  --inst_orphan_elimination               true
% 1.39/0.99  --inst_learning_loop_flag               true
% 1.39/0.99  --inst_learning_start                   3000
% 1.39/0.99  --inst_learning_factor                  2
% 1.39/0.99  --inst_start_prop_sim_after_learn       3
% 1.39/0.99  --inst_sel_renew                        solver
% 1.39/0.99  --inst_lit_activity_flag                true
% 1.39/0.99  --inst_restr_to_given                   false
% 1.39/0.99  --inst_activity_threshold               500
% 1.39/0.99  --inst_out_proof                        true
% 1.39/0.99  
% 1.39/0.99  ------ Resolution Options
% 1.39/0.99  
% 1.39/0.99  --resolution_flag                       false
% 1.39/0.99  --res_lit_sel                           adaptive
% 1.39/0.99  --res_lit_sel_side                      none
% 1.39/0.99  --res_ordering                          kbo
% 1.39/0.99  --res_to_prop_solver                    active
% 1.39/0.99  --res_prop_simpl_new                    false
% 1.39/0.99  --res_prop_simpl_given                  true
% 1.39/0.99  --res_passive_queue_type                priority_queues
% 1.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/0.99  --res_passive_queues_freq               [15;5]
% 1.39/0.99  --res_forward_subs                      full
% 1.39/0.99  --res_backward_subs                     full
% 1.39/0.99  --res_forward_subs_resolution           true
% 1.39/0.99  --res_backward_subs_resolution          true
% 1.39/0.99  --res_orphan_elimination                true
% 1.39/0.99  --res_time_limit                        2.
% 1.39/0.99  --res_out_proof                         true
% 1.39/0.99  
% 1.39/0.99  ------ Superposition Options
% 1.39/0.99  
% 1.39/0.99  --superposition_flag                    true
% 1.39/0.99  --sup_passive_queue_type                priority_queues
% 1.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.39/0.99  --demod_completeness_check              fast
% 1.39/0.99  --demod_use_ground                      true
% 1.39/0.99  --sup_to_prop_solver                    passive
% 1.39/0.99  --sup_prop_simpl_new                    true
% 1.39/0.99  --sup_prop_simpl_given                  true
% 1.39/0.99  --sup_fun_splitting                     false
% 1.39/0.99  --sup_smt_interval                      50000
% 1.39/0.99  
% 1.39/0.99  ------ Superposition Simplification Setup
% 1.39/0.99  
% 1.39/0.99  --sup_indices_passive                   []
% 1.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_full_bw                           [BwDemod]
% 1.39/0.99  --sup_immed_triv                        [TrivRules]
% 1.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_immed_bw_main                     []
% 1.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/0.99  
% 1.39/0.99  ------ Combination Options
% 1.39/0.99  
% 1.39/0.99  --comb_res_mult                         3
% 1.39/0.99  --comb_sup_mult                         2
% 1.39/0.99  --comb_inst_mult                        10
% 1.39/0.99  
% 1.39/0.99  ------ Debug Options
% 1.39/0.99  
% 1.39/0.99  --dbg_backtrace                         false
% 1.39/0.99  --dbg_dump_prop_clauses                 false
% 1.39/0.99  --dbg_dump_prop_clauses_file            -
% 1.39/0.99  --dbg_out_stat                          false
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  ------ Proving...
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  % SZS output start Saturation for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  fof(f4,axiom,(
% 1.39/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f15,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(ennf_transformation,[],[f4])).
% 1.39/0.99  
% 1.39/0.99  fof(f16,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(flattening,[],[f15])).
% 1.39/0.99  
% 1.39/0.99  fof(f21,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(nnf_transformation,[],[f16])).
% 1.39/0.99  
% 1.39/0.99  fof(f22,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(rectify,[],[f21])).
% 1.39/0.99  
% 1.39/0.99  fof(f23,plain,(
% 1.39/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f24,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 1.39/0.99  
% 1.39/0.99  fof(f38,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f24])).
% 1.39/0.99  
% 1.39/0.99  fof(f6,conjecture,(
% 1.39/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f7,negated_conjecture,(
% 1.39/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.39/0.99    inference(negated_conjecture,[],[f6])).
% 1.39/0.99  
% 1.39/0.99  fof(f8,plain,(
% 1.39/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.39/0.99    inference(pure_predicate_removal,[],[f7])).
% 1.39/0.99  
% 1.39/0.99  fof(f9,plain,(
% 1.39/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.39/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.39/0.99  
% 1.39/0.99  fof(f19,plain,(
% 1.39/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : ((((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.39/0.99    inference(ennf_transformation,[],[f9])).
% 1.39/0.99  
% 1.39/0.99  fof(f20,plain,(
% 1.39/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.39/0.99    inference(flattening,[],[f19])).
% 1.39/0.99  
% 1.39/0.99  fof(f32,plain,(
% 1.39/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (((~r2_lattice3(X1,X2,sK6) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,sK6) & r1_lattice3(X0,X2,X3))) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f31,plain,(
% 1.39/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (((~r2_lattice3(X1,sK4,X4) & r2_lattice3(X0,sK4,sK5)) | (~r1_lattice3(X1,sK4,X4) & r1_lattice3(X0,sK4,sK5))) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f30,plain,(
% 1.39/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) => (? [X3,X2] : (? [X4] : (((~r2_lattice3(sK3,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(sK3,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(sK3))) )),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f29,plain,(
% 1.39/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(sK2,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(sK2,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK2))) & ~v2_struct_0(X1)) & l1_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f33,plain,(
% 1.39/0.99    (((((~r2_lattice3(sK3,sK4,sK6) & r2_lattice3(sK2,sK4,sK5)) | (~r1_lattice3(sK3,sK4,sK6) & r1_lattice3(sK2,sK4,sK5))) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK2))) & ~v2_struct_0(sK3)) & l1_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f32,f31,f30,f29])).
% 1.39/0.99  
% 1.39/0.99  fof(f46,plain,(
% 1.39/0.99    l1_orders_2(sK2)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f1,axiom,(
% 1.39/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f10,plain,(
% 1.39/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.39/0.99    inference(ennf_transformation,[],[f1])).
% 1.39/0.99  
% 1.39/0.99  fof(f11,plain,(
% 1.39/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.39/0.99    inference(flattening,[],[f10])).
% 1.39/0.99  
% 1.39/0.99  fof(f34,plain,(
% 1.39/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f11])).
% 1.39/0.99  
% 1.39/0.99  fof(f3,axiom,(
% 1.39/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f14,plain,(
% 1.39/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(ennf_transformation,[],[f3])).
% 1.39/0.99  
% 1.39/0.99  fof(f36,plain,(
% 1.39/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f14])).
% 1.39/0.99  
% 1.39/0.99  fof(f2,axiom,(
% 1.39/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f12,plain,(
% 1.39/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.39/0.99    inference(ennf_transformation,[],[f2])).
% 1.39/0.99  
% 1.39/0.99  fof(f13,plain,(
% 1.39/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.39/0.99    inference(flattening,[],[f12])).
% 1.39/0.99  
% 1.39/0.99  fof(f35,plain,(
% 1.39/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f13])).
% 1.39/0.99  
% 1.39/0.99  fof(f45,plain,(
% 1.39/0.99    ~v2_struct_0(sK2)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f48,plain,(
% 1.39/0.99    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f50,plain,(
% 1.39/0.99    sK5 = sK6),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f37,plain,(
% 1.39/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f24])).
% 1.39/0.99  
% 1.39/0.99  fof(f40,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f24])).
% 1.39/0.99  
% 1.39/0.99  fof(f5,axiom,(
% 1.39/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.39/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f17,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(ennf_transformation,[],[f5])).
% 1.39/0.99  
% 1.39/0.99  fof(f18,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(flattening,[],[f17])).
% 1.39/0.99  
% 1.39/0.99  fof(f25,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(nnf_transformation,[],[f18])).
% 1.39/0.99  
% 1.39/0.99  fof(f26,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(rectify,[],[f25])).
% 1.39/0.99  
% 1.39/0.99  fof(f27,plain,(
% 1.39/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f28,plain,(
% 1.39/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.39/0.99  
% 1.39/0.99  fof(f42,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f28])).
% 1.39/0.99  
% 1.39/0.99  fof(f41,plain,(
% 1.39/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f28])).
% 1.39/0.99  
% 1.39/0.99  fof(f44,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f28])).
% 1.39/0.99  
% 1.39/0.99  fof(f39,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f24])).
% 1.39/0.99  
% 1.39/0.99  fof(f43,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f28])).
% 1.39/0.99  
% 1.39/0.99  fof(f51,plain,(
% 1.39/0.99    r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f52,plain,(
% 1.39/0.99    r2_lattice3(sK2,sK4,sK5) | ~r1_lattice3(sK3,sK4,sK6)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f53,plain,(
% 1.39/0.99    ~r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f47,plain,(
% 1.39/0.99    ~v2_struct_0(sK3)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f54,plain,(
% 1.39/0.99    ~r2_lattice3(sK3,sK4,sK6) | ~r1_lattice3(sK3,sK4,sK6)),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  fof(f49,plain,(
% 1.39/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.39/0.99    inference(cnf_transformation,[],[f33])).
% 1.39/0.99  
% 1.39/0.99  cnf(c_196,plain,
% 1.39/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.39/0.99      theory(equality) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_195,plain,
% 1.39/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.39/0.99      theory(equality) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_192,plain,
% 1.39/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.39/0.99      theory(equality) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2443,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_5,plain,
% 1.39/0.99      ( r1_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_19,negated_conjecture,
% 1.39/0.99      ( l1_orders_2(sK2) ),
% 1.39/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_407,plain,
% 1.39/0.99      ( r1_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_408,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2429,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_408]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2800,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_0,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.39/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2,plain,
% 1.39/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_1,plain,
% 1.39/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.39/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_220,plain,
% 1.39/0.99      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.39/0.99      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_20,negated_conjecture,
% 1.39/0.99      ( ~ v2_struct_0(sK2) ),
% 1.39/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_270,plain,
% 1.39/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_220,c_20]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_271,plain,
% 1.39/0.99      ( ~ l1_orders_2(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_270]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_273,plain,
% 1.39/0.99      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_271,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_301,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | u1_struct_0(sK2) != X1 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_273]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_302,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2)) | r2_hidden(X0,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2435,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | r2_hidden(X0_45,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_302]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2794,plain,
% 1.39/0.99      ( m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X0_45,u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3633,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK0(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2800,c_2794]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_17,negated_conjecture,
% 1.39/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2436,negated_conjecture,
% 1.39/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2793,plain,
% 1.39/0.99      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_15,negated_conjecture,
% 1.39/0.99      ( sK5 = sK6 ),
% 1.39/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2438,negated_conjecture,
% 1.39/0.99      ( sK5 = sK6 ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2808,plain,
% 1.39/0.99      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(light_normalisation,[status(thm)],[c_2793,c_2438]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_6,plain,
% 1.39/0.99      ( r1_orders_2(X0,X1,X2)
% 1.39/0.99      | ~ r1_lattice3(X0,X3,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | ~ r2_hidden(X2,X3)
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_386,plain,
% 1.39/0.99      ( r1_orders_2(X0,X1,X2)
% 1.39/0.99      | ~ r1_lattice3(X0,X3,X1)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/0.99      | ~ r2_hidden(X2,X3)
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_387,plain,
% 1.39/0.99      ( r1_orders_2(sK2,X0,X1)
% 1.39/0.99      | ~ r1_lattice3(sK2,X2,X0)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.39/0.99      | ~ r2_hidden(X1,X2) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2430,plain,
% 1.39/0.99      ( r1_orders_2(sK2,X0_45,X1_45)
% 1.39/0.99      | ~ r1_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.39/0.99      | ~ r2_hidden(X1_45,X0_46) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_387]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2799,plain,
% 1.39/0.99      ( r1_orders_2(sK2,X0_45,X1_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X0_46) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2430]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3528,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,X0_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X0_45,X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2808,c_2799]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3629,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK0(sK2,X0_46,X0_45),X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2800,c_3528]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4024,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_3633,c_3629]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3,plain,
% 1.39/0.99      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 1.39/0.99      | r1_lattice3(X0,X2,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_437,plain,
% 1.39/0.99      ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
% 1.39/0.99      | r1_lattice3(X0,X2,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_438,plain,
% 1.39/0.99      ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
% 1.39/0.99      | r1_lattice3(sK2,X1,X0)
% 1.39/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2427,plain,
% 1.39/0.99      ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45))
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_438]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2802,plain,
% 1.39/0.99      ( r1_orders_2(sK2,X0_45,sK0(sK2,X0_46,X0_45)) != iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2427]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4893,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_4024,c_2802]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4898,plain,
% 1.39/0.99      ( r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,sK6) = iProver_top ),
% 1.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4893,c_2808]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4899,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
% 1.39/0.99      inference(renaming,[status(thm)],[c_4898]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_9,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_341,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_342,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_341]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2433,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_342]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2796,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3240,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK1(sK2,X0_46,X0_45),u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2796,c_2794]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_10,plain,
% 1.39/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/0.99      | r1_orders_2(X0,X3,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.39/0.99      | ~ r2_hidden(X3,X1)
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_320,plain,
% 1.39/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/0.99      | r1_orders_2(X0,X3,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.39/0.99      | ~ r2_hidden(X3,X1)
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_321,plain,
% 1.39/0.99      ( ~ r2_lattice3(sK2,X0,X1)
% 1.39/0.99      | r1_orders_2(sK2,X2,X1)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | ~ r2_hidden(X2,X0) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2434,plain,
% 1.39/0.99      ( ~ r2_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | r1_orders_2(sK2,X1_45,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
% 1.39/0.99      | ~ r2_hidden(X1_45,X0_46) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_321]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2795,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,X1_45,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X0_46) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2434]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3312,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,X0_45,sK6) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X0_45,X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2808,c_2795]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3402,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2796,c_3312]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3997,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_3240,c_3402]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_7,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_371,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_372,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0,X1)
% 1.39/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_371]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2431,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_372]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2798,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X0_45) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2431]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4531,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_3997,c_2798]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4619,plain,
% 1.39/0.99      ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | r2_lattice3(sK2,X0_46,sK6) = iProver_top ),
% 1.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4531,c_2808]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4620,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top ),
% 1.39/0.99      inference(renaming,[status(thm)],[c_4619]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3631,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK0(sK2,X1_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK0(sK2,X1_46,X0_45),X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2800,c_3312]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4213,plain,
% 1.39/0.99      ( r2_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_3633,c_3631]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4,plain,
% 1.39/0.99      ( r1_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_422,plain,
% 1.39/0.99      ( r1_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_423,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | r2_hidden(sK0(sK2,X0,X1),X0) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2428,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_423]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2801,plain,
% 1.39/0.99      ( r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK0(sK2,X0_46,X0_45),X0_46) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_4212,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2801,c_3631]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3562,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK1(sK2,X0_46,X0_45),X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2796,c_3528]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3996,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,u1_struct_0(sK2),sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_3240,c_3562]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3900,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK0(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2801,c_3629]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_8,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.39/0.99      | ~ l1_orders_2(X0) ),
% 1.39/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_356,plain,
% 1.39/0.99      ( r2_lattice3(X0,X1,X2)
% 1.39/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.39/0.99      | sK2 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_357,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0,X1)
% 1.39/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/0.99      | r2_hidden(sK1(sK2,X0,X1),X0) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2432,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45)
% 1.39/0.99      | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
% 1.39/0.99      | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_357]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2797,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(sK1(sK2,X0_46,X0_45),X0_46) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3890,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK6,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2797,c_3562]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3789,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),sK6) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2797,c_3402]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_14,negated_conjecture,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 1.39/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2439,negated_conjecture,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2791,plain,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2811,plain,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 1.39/0.99      inference(light_normalisation,[status(thm)],[c_2791,c_2438]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3401,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.39/0.99      | r2_hidden(sK6,X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2808,c_3312]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3429,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top
% 1.39/0.99      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2811,c_3401]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3561,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,sK6) != iProver_top
% 1.39/0.99      | r2_hidden(sK6,X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2808,c_3528]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3580,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK6) != iProver_top
% 1.39/0.99      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.39/0.99      inference(instantiation,[status(thm)],[c_3561]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3777,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK6,sK6) = iProver_top
% 1.39/0.99      | r2_hidden(sK6,sK4) != iProver_top ),
% 1.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3429,c_3580]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3632,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,sK0(sK2,X1_46,X0_45)) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,X1_45,sK0(sK2,X1_46,X0_45)) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,X0_45) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X0_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2800,c_2795]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3630,plain,
% 1.39/0.99      ( r1_orders_2(sK2,sK0(sK2,X0_46,X0_45),X1_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,sK0(sK2,X0_46,X0_45)) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2800,c_2799]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3529,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r1_orders_2(sK2,sK1(sK2,X0_46,X0_45),X1_45) = iProver_top
% 1.39/0.99      | r1_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2796,c_2799]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3313,plain,
% 1.39/0.99      ( r2_lattice3(sK2,X0_46,X0_45) = iProver_top
% 1.39/0.99      | r2_lattice3(sK2,X1_46,sK1(sK2,X0_46,X0_45)) != iProver_top
% 1.39/0.99      | r1_orders_2(sK2,X1_45,sK1(sK2,X0_46,X0_45)) = iProver_top
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | m1_subset_1(X1_45,u1_struct_0(sK2)) != iProver_top
% 1.39/0.99      | r2_hidden(X1_45,X1_46) != iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2796,c_2795]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_3123,plain,
% 1.39/0.99      ( r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.39/0.99      inference(superposition,[status(thm)],[c_2808,c_2794]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_13,negated_conjecture,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.39/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2440,negated_conjecture,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2790,plain,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 1.39/0.99      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2821,plain,
% 1.39/0.99      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 1.39/0.99      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.39/0.99      inference(light_normalisation,[status(thm)],[c_2790,c_2438]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_12,negated_conjecture,
% 1.39/0.99      ( ~ r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5) ),
% 1.39/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2441,negated_conjecture,
% 1.39/0.99      ( ~ r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2789,plain,
% 1.39/0.99      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2816,plain,
% 1.39/0.99      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.39/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 1.39/0.99      inference(light_normalisation,[status(thm)],[c_2789,c_2438]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_18,negated_conjecture,
% 1.39/0.99      ( ~ v2_struct_0(sK3) ),
% 1.39/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_260,plain,
% 1.39/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_220,c_18]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_261,plain,
% 1.39/0.99      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_260]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_286,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,X1)
% 1.39/0.99      | r2_hidden(X0,X1)
% 1.39/0.99      | ~ l1_orders_2(sK3)
% 1.39/0.99      | u1_struct_0(sK3) != X1 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_261]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_287,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.39/0.99      | r2_hidden(X0,u1_struct_0(sK3))
% 1.39/0.99      | ~ l1_orders_2(sK3) ),
% 1.39/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_452,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.39/0.99      | r2_hidden(X0,u1_struct_0(sK3))
% 1.39/0.99      | sK2 != sK3 ),
% 1.39/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_287]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2426,plain,
% 1.39/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK3))
% 1.39/0.99      | r2_hidden(X0_45,u1_struct_0(sK3))
% 1.39/0.99      | sK2 != sK3 ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_452]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2803,plain,
% 1.39/0.99      ( sK2 != sK3
% 1.39/0.99      | m1_subset_1(X0_45,u1_struct_0(sK3)) != iProver_top
% 1.39/0.99      | r2_hidden(X0_45,u1_struct_0(sK3)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2426]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_11,negated_conjecture,
% 1.39/0.99      ( ~ r2_lattice3(sK3,sK4,sK6) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.39/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2442,negated_conjecture,
% 1.39/0.99      ( ~ r2_lattice3(sK3,sK4,sK6) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2788,plain,
% 1.39/0.99      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 1.39/0.99      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2442]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_16,negated_conjecture,
% 1.39/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.39/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2437,negated_conjecture,
% 1.39/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2792,plain,
% 1.39/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2437]) ).
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  % SZS output end Saturation for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  ------                               Statistics
% 1.39/0.99  
% 1.39/0.99  ------ General
% 1.39/0.99  
% 1.39/0.99  abstr_ref_over_cycles:                  0
% 1.39/0.99  abstr_ref_under_cycles:                 0
% 1.39/0.99  gc_basic_clause_elim:                   0
% 1.39/0.99  forced_gc_time:                         0
% 1.39/0.99  parsing_time:                           0.012
% 1.39/0.99  unif_index_cands_time:                  0.
% 1.39/0.99  unif_index_add_time:                    0.
% 1.39/0.99  orderings_time:                         0.
% 1.39/0.99  out_proof_time:                         0.
% 1.39/0.99  total_time:                             0.17
% 1.39/0.99  num_of_symbols:                         48
% 1.39/0.99  num_of_terms:                           3432
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing
% 1.39/0.99  
% 1.39/0.99  num_of_splits:                          0
% 1.39/0.99  num_of_split_atoms:                     0
% 1.39/0.99  num_of_reused_defs:                     0
% 1.39/0.99  num_eq_ax_congr_red:                    17
% 1.39/0.99  num_of_sem_filtered_clauses:            1
% 1.39/0.99  num_of_subtypes:                        3
% 1.39/0.99  monotx_restored_types:                  0
% 1.39/0.99  sat_num_of_epr_types:                   0
% 1.39/0.99  sat_num_of_non_cyclic_types:            0
% 1.39/0.99  sat_guarded_non_collapsed_types:        0
% 1.39/0.99  num_pure_diseq_elim:                    0
% 1.39/0.99  simp_replaced_by:                       0
% 1.39/0.99  res_preprocessed:                       99
% 1.39/0.99  prep_upred:                             0
% 1.39/0.99  prep_unflattend:                        137
% 1.39/0.99  smt_new_axioms:                         0
% 1.39/0.99  pred_elim_cands:                        5
% 1.39/0.99  pred_elim:                              4
% 1.39/0.99  pred_elim_cl:                           4
% 1.39/0.99  pred_elim_cycles:                       13
% 1.39/0.99  merged_defs:                            0
% 1.39/0.99  merged_defs_ncl:                        0
% 1.39/0.99  bin_hyper_res:                          0
% 1.39/0.99  prep_cycles:                            4
% 1.39/0.99  pred_elim_time:                         0.036
% 1.39/0.99  splitting_time:                         0.
% 1.39/0.99  sem_filter_time:                        0.
% 1.39/0.99  monotx_time:                            0.
% 1.39/0.99  subtype_inf_time:                       0.
% 1.39/0.99  
% 1.39/0.99  ------ Problem properties
% 1.39/0.99  
% 1.39/0.99  clauses:                                17
% 1.39/0.99  conjectures:                            7
% 1.39/0.99  epr:                                    5
% 1.39/0.99  horn:                                   12
% 1.39/0.99  ground:                                 7
% 1.39/0.99  unary:                                  3
% 1.39/0.99  binary:                                 5
% 1.39/0.99  lits:                                   44
% 1.39/0.99  lits_eq:                                2
% 1.39/0.99  fd_pure:                                0
% 1.39/0.99  fd_pseudo:                              0
% 1.39/0.99  fd_cond:                                0
% 1.39/0.99  fd_pseudo_cond:                         0
% 1.39/0.99  ac_symbols:                             0
% 1.39/0.99  
% 1.39/0.99  ------ Propositional Solver
% 1.39/0.99  
% 1.39/0.99  prop_solver_calls:                      27
% 1.39/0.99  prop_fast_solver_calls:                 1259
% 1.39/0.99  smt_solver_calls:                       0
% 1.39/0.99  smt_fast_solver_calls:                  0
% 1.39/0.99  prop_num_of_clauses:                    969
% 1.39/0.99  prop_preprocess_simplified:             4121
% 1.39/0.99  prop_fo_subsumed:                       46
% 1.39/0.99  prop_solver_time:                       0.
% 1.39/0.99  smt_solver_time:                        0.
% 1.39/0.99  smt_fast_solver_time:                   0.
% 1.39/0.99  prop_fast_solver_time:                  0.
% 1.39/0.99  prop_unsat_core_time:                   0.
% 1.39/0.99  
% 1.39/0.99  ------ QBF
% 1.39/0.99  
% 1.39/0.99  qbf_q_res:                              0
% 1.39/0.99  qbf_num_tautologies:                    0
% 1.39/0.99  qbf_prep_cycles:                        0
% 1.39/0.99  
% 1.39/0.99  ------ BMC1
% 1.39/0.99  
% 1.39/0.99  bmc1_current_bound:                     -1
% 1.39/0.99  bmc1_last_solved_bound:                 -1
% 1.39/0.99  bmc1_unsat_core_size:                   -1
% 1.39/0.99  bmc1_unsat_core_parents_size:           -1
% 1.39/0.99  bmc1_merge_next_fun:                    0
% 1.39/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.39/0.99  
% 1.39/0.99  ------ Instantiation
% 1.39/0.99  
% 1.39/0.99  inst_num_of_clauses:                    248
% 1.39/0.99  inst_num_in_passive:                    3
% 1.39/0.99  inst_num_in_active:                     205
% 1.39/0.99  inst_num_in_unprocessed:                40
% 1.39/0.99  inst_num_of_loops:                      220
% 1.39/0.99  inst_num_of_learning_restarts:          0
% 1.39/0.99  inst_num_moves_active_passive:          10
% 1.39/0.99  inst_lit_activity:                      0
% 1.39/0.99  inst_lit_activity_moves:                0
% 1.39/0.99  inst_num_tautologies:                   0
% 1.39/0.99  inst_num_prop_implied:                  0
% 1.39/0.99  inst_num_existing_simplified:           0
% 1.39/0.99  inst_num_eq_res_simplified:             0
% 1.39/0.99  inst_num_child_elim:                    0
% 1.39/0.99  inst_num_of_dismatching_blockings:      231
% 1.39/0.99  inst_num_of_non_proper_insts:           470
% 1.39/0.99  inst_num_of_duplicates:                 0
% 1.39/0.99  inst_inst_num_from_inst_to_res:         0
% 1.39/0.99  inst_dismatching_checking_time:         0.
% 1.39/0.99  
% 1.39/0.99  ------ Resolution
% 1.39/0.99  
% 1.39/0.99  res_num_of_clauses:                     0
% 1.39/0.99  res_num_in_passive:                     0
% 1.39/0.99  res_num_in_active:                      0
% 1.39/0.99  res_num_of_loops:                       103
% 1.39/0.99  res_forward_subset_subsumed:            41
% 1.39/0.99  res_backward_subset_subsumed:           0
% 1.39/0.99  res_forward_subsumed:                   8
% 1.39/0.99  res_backward_subsumed:                  0
% 1.39/0.99  res_forward_subsumption_resolution:     6
% 1.39/0.99  res_backward_subsumption_resolution:    0
% 1.39/0.99  res_clause_to_clause_subsumption:       225
% 1.39/0.99  res_orphan_elimination:                 0
% 1.39/0.99  res_tautology_del:                      57
% 1.39/0.99  res_num_eq_res_simplified:              0
% 1.39/0.99  res_num_sel_changes:                    0
% 1.39/0.99  res_moves_from_active_to_pass:          0
% 1.39/0.99  
% 1.39/0.99  ------ Superposition
% 1.39/0.99  
% 1.39/0.99  sup_time_total:                         0.
% 1.39/0.99  sup_time_generating:                    0.
% 1.39/0.99  sup_time_sim_full:                      0.
% 1.39/0.99  sup_time_sim_immed:                     0.
% 1.39/0.99  
% 1.39/0.99  sup_num_of_clauses:                     45
% 1.39/0.99  sup_num_in_active:                      43
% 1.39/0.99  sup_num_in_passive:                     2
% 1.39/0.99  sup_num_of_loops:                       43
% 1.39/0.99  sup_fw_superposition:                   15
% 1.39/0.99  sup_bw_superposition:                   13
% 1.39/0.99  sup_immediate_simplified:               0
% 1.39/0.99  sup_given_eliminated:                   0
% 1.39/0.99  comparisons_done:                       0
% 1.39/0.99  comparisons_avoided:                    0
% 1.39/0.99  
% 1.39/0.99  ------ Simplifications
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  sim_fw_subset_subsumed:                 0
% 1.39/0.99  sim_bw_subset_subsumed:                 0
% 1.39/0.99  sim_fw_subsumed:                        0
% 1.39/0.99  sim_bw_subsumed:                        0
% 1.39/0.99  sim_fw_subsumption_res:                 0
% 1.39/0.99  sim_bw_subsumption_res:                 0
% 1.39/0.99  sim_tautology_del:                      2
% 1.39/0.99  sim_eq_tautology_del:                   0
% 1.39/0.99  sim_eq_res_simp:                        0
% 1.39/0.99  sim_fw_demodulated:                     0
% 1.39/0.99  sim_bw_demodulated:                     0
% 1.39/0.99  sim_light_normalised:                   4
% 1.39/0.99  sim_joinable_taut:                      0
% 1.39/0.99  sim_joinable_simp:                      0
% 1.39/0.99  sim_ac_normalised:                      0
% 1.39/0.99  sim_smt_subsumption:                    0
% 1.39/0.99  
%------------------------------------------------------------------------------
