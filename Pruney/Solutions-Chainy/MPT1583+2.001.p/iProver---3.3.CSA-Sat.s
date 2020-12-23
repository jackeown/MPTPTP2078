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

% Result     : CounterSatisfiable 1.93s
% Output     : Saturation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  250 (3044 expanded)
%              Number of clauses        :  186 ( 807 expanded)
%              Number of leaves         :   17 ( 827 expanded)
%              Depth                    :   20
%              Number of atoms          :  940 (23749 expanded)
%              Number of equality atoms :  378 (2743 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ( ~ r2_lattice3(X1,X2,X4)
              & r2_lattice3(X0,X2,X3) )
            | ( ~ r1_lattice3(X1,X2,X4)
              & r1_lattice3(X0,X2,X3) ) )
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ( ( ~ r2_lattice3(X1,X2,sK7)
            & r2_lattice3(X0,X2,X3) )
          | ( ~ r1_lattice3(X1,X2,sK7)
            & r1_lattice3(X0,X2,X3) ) )
        & sK7 = X3
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
            ( ( ( ~ r2_lattice3(X1,sK5,X4)
                & r2_lattice3(X0,sK5,sK6) )
              | ( ~ r1_lattice3(X1,sK5,X4)
                & r1_lattice3(X0,sK5,sK6) ) )
            & sK6 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
                ( ( ( ~ r2_lattice3(sK4,X2,X4)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(sK4,X2,X4)
                    & r1_lattice3(X0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK4)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
                      & r2_lattice3(sK3,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK3,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ( ~ r2_lattice3(sK4,sK5,sK7)
        & r2_lattice3(sK3,sK5,sK6) )
      | ( ~ r1_lattice3(sK4,sK5,sK7)
        & r1_lattice3(sK3,sK5,sK6) ) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & ~ v2_struct_0(sK4)
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f38,f37,f36,f35])).

fof(f57,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,
    ( r2_lattice3(sK3,sK5,sK6)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,
    ( r2_lattice3(sK3,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_253,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_252,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2675,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_10,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_413,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_414,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_2655,plain,
    ( r1_lattice3(sK3,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_3121,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2655])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2670,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | r2_hidden(X0_46,X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3107,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | r2_hidden(X0_46,X1_46) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2670])).

cnf(c_4333,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_3107])).

cnf(c_27,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_282,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_310,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_282,c_25])).

cnf(c_311,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_312,plain,
    ( l1_orders_2(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_4745,plain,
    ( r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X0_46,X1_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4333,c_27,c_312])).

cnf(c_4746,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4745])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_392,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_393,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r1_lattice3(sK3,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_2656,plain,
    ( r1_orders_2(sK3,X0_46,X1_46)
    | ~ r1_lattice3(sK3,X2_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | ~ r2_hidden(X1_46,X2_46) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_3120,plain,
    ( r1_orders_2(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,X2_46,X0_46) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_46,X2_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2656])).

cnf(c_4332,plain,
    ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X3_46,X0_46) != iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X1_46,X2_46),X3_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_3120])).

cnf(c_5746,plain,
    ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_4332])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_377,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_378,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK2(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_2657,plain,
    ( r2_lattice3(sK3,X0_46,X1_46)
    | ~ r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_3119,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),X1_46) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2657])).

cnf(c_6177,plain,
    ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X1_46,X2_46),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5746,c_3119])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_347,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_348,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_2659,plain,
    ( r2_lattice3(sK3,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_3117,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_6276,plain,
    ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6177,c_3121,c_3117])).

cnf(c_4243,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_3107])).

cnf(c_4733,plain,
    ( r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_lattice3(sK3,X0_46,X1_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4243,c_27,c_312])).

cnf(c_4734,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_4242,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,X3_46,X2_46) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,X1_46),X3_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_3120])).

cnf(c_5626,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X2_46) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_4242])).

cnf(c_6125,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5626,c_3119])).

cnf(c_2715,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_6257,plain,
    ( m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6125,c_2715])).

cnf(c_6258,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6257])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,sK1(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_443,plain,
    ( ~ r1_orders_2(X0,X1,sK1(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_444,plain,
    ( ~ r1_orders_2(sK3,X0,sK1(sK3,X1,X0))
    | r1_lattice3(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_2653,plain,
    ( ~ r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X0_46))
    | r1_lattice3(sK3,X1_46,X0_46)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_3123,plain,
    ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X0_46)) != iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2653])).

cnf(c_6176,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X1_46) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5746,c_3123])).

cnf(c_9,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_428,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_429,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_2654,plain,
    ( r1_lattice3(sK3,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0_46,X1_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_3122,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_46,X1_46),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2654])).

cnf(c_5745,plain,
    ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_4332])).

cnf(c_5801,plain,
    ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | r1_lattice3(sK3,X1_46,sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X1_46,X2_46),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5745,c_3119])).

cnf(c_6114,plain,
    ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | r1_lattice3(sK3,X1_46,sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5801,c_3121,c_3117])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_362,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_363,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_2658,plain,
    ( r2_lattice3(sK3,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | r2_hidden(sK2(sK3,X0_46,X1_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_3118,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,X1_46),X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2658])).

cnf(c_5625,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,X0_46,X2_46) != iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_4242])).

cnf(c_5734,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5625,c_3119])).

cnf(c_5820,plain,
    ( m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5734,c_2715])).

cnf(c_5821,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5820])).

cnf(c_19,negated_conjecture,
    ( r2_lattice3(sK3,sK5,sK6)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2666,negated_conjecture,
    ( r2_lattice3(sK3,sK5,sK6)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3111,plain,
    ( r2_lattice3(sK3,sK5,sK6) = iProver_top
    | r1_lattice3(sK3,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2666])).

cnf(c_20,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2665,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3150,plain,
    ( r2_lattice3(sK3,sK5,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3111,c_2665])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_326,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_327,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_2660,plain,
    ( ~ r2_lattice3(sK3,X0_46,X1_46)
    | r1_orders_2(sK3,X2_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_46,u1_struct_0(sK3))
    | ~ r2_hidden(X2_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_3116,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) != iProver_top
    | r1_orders_2(sK3,X2_46,X1_46) = iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2_46,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2660])).

cnf(c_3782,plain,
    ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_46,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_3116])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2663,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3113,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2663])).

cnf(c_3129,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3113,c_2665])).

cnf(c_4373,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r1_orders_2(sK3,X0_46,sK7) = iProver_top
    | r2_hidden(X0_46,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3782,c_3129])).

cnf(c_4374,plain,
    ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_46,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4373])).

cnf(c_4385,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,X1_46),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_4374])).

cnf(c_5461,plain,
    ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4385,c_3119])).

cnf(c_5464,plain,
    ( r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r2_lattice3(sK3,X0_46,sK7) = iProver_top
    | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5461,c_3129])).

cnf(c_5465,plain,
    ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_5464])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2674,plain,
    ( r2_hidden(sK0(X0_46),X0_46)
    | v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3103,plain,
    ( r2_hidden(sK0(X0_46),X0_46) = iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2674])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_152,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_1])).

cnf(c_153,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_2662,plain,
    ( m1_subset_1(X0_46,X1_46)
    | ~ r2_hidden(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_3114,plain,
    ( m1_subset_1(X0_46,X1_46) = iProver_top
    | r2_hidden(X0_46,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2662])).

cnf(c_3935,plain,
    ( m1_subset_1(sK0(X0_46),X0_46) = iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3103,c_3114])).

cnf(c_4029,plain,
    ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_3120])).

cnf(c_5174,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
    | r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_27,c_312])).

cnf(c_5175,plain,
    ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_5174])).

cnf(c_5184,plain,
    ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3103,c_5175])).

cnf(c_5220,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
    | r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5184,c_27,c_312])).

cnf(c_5221,plain,
    ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5220])).

cnf(c_5229,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK0(u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5221,c_3119])).

cnf(c_3399,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2674])).

cnf(c_3400,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3399])).

cnf(c_3336,plain,
    ( m1_subset_1(X0_46,u1_struct_0(sK3))
    | ~ r2_hidden(X0_46,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_3496,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_3497,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3496])).

cnf(c_3662,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_3668,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3662])).

cnf(c_5358,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK0(u1_struct_0(sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5229,c_27,c_312,c_3400,c_3497,c_3668])).

cnf(c_2673,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | ~ v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3104,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | v1_xboole_0(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2673])).

cnf(c_4222,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_3104])).

cnf(c_4634,plain,
    ( r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_4222])).

cnf(c_5306,plain,
    ( v1_xboole_0(X0_46) != iProver_top
    | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4634,c_27,c_312])).

cnf(c_5307,plain,
    ( r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_5306])).

cnf(c_4170,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3104])).

cnf(c_4503,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_4170])).

cnf(c_5296,plain,
    ( v1_xboole_0(X0_46) != iProver_top
    | r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4503,c_27,c_312])).

cnf(c_5297,plain,
    ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_5296])).

cnf(c_4387,plain,
    ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_4374])).

cnf(c_5046,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_27,c_312])).

cnf(c_5047,plain,
    ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_5046])).

cnf(c_4632,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_4222])).

cnf(c_4631,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,X2_46,sK1(sK3,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_4222])).

cnf(c_4630,plain,
    ( r1_lattice3(sK3,X0_46,sK7) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_4222])).

cnf(c_3869,plain,
    ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
    | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,X1_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3120])).

cnf(c_4028,plain,
    ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
    | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK7,X0_46) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3935,c_3869])).

cnf(c_4580,plain,
    ( r2_hidden(sK7,X0_46) != iProver_top
    | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
    | r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4028,c_27,c_312])).

cnf(c_4581,plain,
    ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
    | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK7,X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_4580])).

cnf(c_4501,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_4170])).

cnf(c_4500,plain,
    ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
    | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
    | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_4170])).

cnf(c_4499,plain,
    ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_4170])).

cnf(c_4383,plain,
    ( r1_orders_2(sK3,sK7,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | r2_hidden(sK7,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_4374])).

cnf(c_3887,plain,
    ( r1_orders_2(sK3,sK7,sK7) = iProver_top
    | r1_lattice3(sK3,X0_46,sK7) != iProver_top
    | r2_hidden(sK7,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3869])).

cnf(c_3896,plain,
    ( r1_orders_2(sK3,sK7,sK7) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) != iProver_top
    | r2_hidden(sK7,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3887])).

cnf(c_4489,plain,
    ( r1_orders_2(sK3,sK7,sK7) = iProver_top
    | r2_hidden(sK7,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_3896])).

cnf(c_4384,plain,
    ( r1_orders_2(sK3,sK1(sK3,X0_46,X1_46),sK7) = iProver_top
    | r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_46,X1_46),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_4374])).

cnf(c_4331,plain,
    ( r1_orders_2(sK3,sK1(sK3,X0_46,X1_46),sK7) = iProver_top
    | r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_lattice3(sK3,X2_46,sK1(sK3,X0_46,X1_46)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_3869])).

cnf(c_4241,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),sK7) = iProver_top
    | r1_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) != iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK7,X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_3869])).

cnf(c_4221,plain,
    ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_46,X1_46),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_3114])).

cnf(c_4169,plain,
    ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
    | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X0_46,X1_46),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_3114])).

cnf(c_3597,plain,
    ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3107])).

cnf(c_4158,plain,
    ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_27,c_312])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2664,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3112,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2664])).

cnf(c_3596,plain,
    ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3112,c_3107])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2671,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | ~ v1_xboole_0(X1_46)
    | v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3106,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | v1_xboole_0(X1_46) != iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2671])).

cnf(c_3549,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3112,c_3106])).

cnf(c_18,negated_conjecture,
    ( r2_lattice3(sK3,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2667,negated_conjecture,
    ( r2_lattice3(sK3,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3110,plain,
    ( r2_lattice3(sK3,sK5,sK6) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2667])).

cnf(c_3160,plain,
    ( r2_lattice3(sK3,sK5,sK7) = iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3110,c_2665])).

cnf(c_17,negated_conjecture,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2668,negated_conjecture,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | r1_lattice3(sK3,sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3109,plain,
    ( r2_lattice3(sK4,sK5,sK7) != iProver_top
    | r1_lattice3(sK3,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2668])).

cnf(c_3155,plain,
    ( r2_lattice3(sK4,sK5,sK7) != iProver_top
    | r1_lattice3(sK3,sK5,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3109,c_2665])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_300,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_282,c_23])).

cnf(c_301,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_458,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | sK3 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_301])).

cnf(c_2652,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | sK3 != sK4 ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_3124,plain,
    ( sK3 != sK4
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2652])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2672,plain,
    ( m1_subset_1(X0_46,X1_46)
    | ~ v1_xboole_0(X1_46)
    | ~ v1_xboole_0(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3105,plain,
    ( m1_subset_1(X0_46,X1_46) = iProver_top
    | v1_xboole_0(X1_46) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2672])).

cnf(c_313,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_24])).

cnf(c_2661,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_313])).

cnf(c_3115,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_16,negated_conjecture,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2669,negated_conjecture,
    ( ~ r2_lattice3(sK4,sK5,sK7)
    | ~ r1_lattice3(sK4,sK5,sK7) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3108,plain,
    ( r2_lattice3(sK4,sK5,sK7) != iProver_top
    | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2669])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.93/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.99  
% 1.93/0.99  ------  iProver source info
% 1.93/0.99  
% 1.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.99  git: non_committed_changes: false
% 1.93/0.99  git: last_make_outside_of_git: false
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     num_symb
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       true
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  ------ Parsing...
% 1.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.99  ------ Proving...
% 1.93/0.99  ------ Problem Properties 
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  clauses                                 23
% 1.93/0.99  conjectures                             7
% 1.93/0.99  EPR                                     10
% 1.93/0.99  Horn                                    16
% 1.93/0.99  unary                                   4
% 1.93/0.99  binary                                  8
% 1.93/0.99  lits                                    57
% 1.93/0.99  lits eq                                 2
% 1.93/0.99  fd_pure                                 0
% 1.93/0.99  fd_pseudo                               0
% 1.93/0.99  fd_cond                                 0
% 1.93/0.99  fd_pseudo_cond                          0
% 1.93/0.99  AC symbols                              0
% 1.93/0.99  
% 1.93/0.99  ------ Schedule dynamic 5 is on 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  Current options:
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     none
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       false
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ Proving...
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  % SZS output start Saturation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  fof(f6,axiom,(
% 1.93/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f16,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(ennf_transformation,[],[f6])).
% 1.93/0.99  
% 1.93/0.99  fof(f17,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(flattening,[],[f16])).
% 1.93/0.99  
% 1.93/0.99  fof(f27,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f17])).
% 1.93/0.99  
% 1.93/0.99  fof(f28,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(rectify,[],[f27])).
% 1.93/0.99  
% 1.93/0.99  fof(f29,plain,(
% 1.93/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f30,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 1.93/0.99  
% 1.93/0.99  fof(f49,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f8,conjecture,(
% 1.93/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f9,negated_conjecture,(
% 1.93/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.93/0.99    inference(negated_conjecture,[],[f8])).
% 1.93/0.99  
% 1.93/0.99  fof(f10,plain,(
% 1.93/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((v4_yellow_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.93/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.93/0.99  
% 1.93/0.99  fof(f11,plain,(
% 1.93/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (~v2_struct_0(X1) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4))))))))),
% 1.93/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.93/0.99  
% 1.93/0.99  fof(f20,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : ((((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f11])).
% 1.93/0.99  
% 1.93/0.99  fof(f21,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f38,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (((~r2_lattice3(X1,X2,sK7) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,sK7) & r1_lattice3(X0,X2,X3))) & sK7 = X3 & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f37,plain,(
% 1.93/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (((~r2_lattice3(X1,sK5,X4) & r2_lattice3(X0,sK5,sK6)) | (~r1_lattice3(X1,sK5,X4) & r1_lattice3(X0,sK5,sK6))) & sK6 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f36,plain,(
% 1.93/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) => (? [X3,X2] : (? [X4] : (((~r2_lattice3(sK4,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(sK4,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(sK4))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f35,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (((~r2_lattice3(X1,X2,X4) & r2_lattice3(sK3,X2,X3)) | (~r1_lattice3(X1,X2,X4) & r1_lattice3(sK3,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK3))) & ~v2_struct_0(X1)) & l1_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f39,plain,(
% 1.93/0.99    (((((~r2_lattice3(sK4,sK5,sK7) & r2_lattice3(sK3,sK5,sK6)) | (~r1_lattice3(sK4,sK5,sK7) & r1_lattice3(sK3,sK5,sK6))) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & ~v2_struct_0(sK4)) & l1_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f38,f37,f36,f35])).
% 1.93/0.99  
% 1.93/0.99  fof(f57,plain,(
% 1.93/0.99    l1_orders_2(sK3)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f3,axiom,(
% 1.93/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f12,plain,(
% 1.93/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f3])).
% 1.93/0.99  
% 1.93/0.99  fof(f26,plain,(
% 1.93/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.93/0.99    inference(nnf_transformation,[],[f12])).
% 1.93/0.99  
% 1.93/0.99  fof(f42,plain,(
% 1.93/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f5,axiom,(
% 1.93/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f15,plain,(
% 1.93/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(ennf_transformation,[],[f5])).
% 1.93/0.99  
% 1.93/0.99  fof(f47,plain,(
% 1.93/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f15])).
% 1.93/0.99  
% 1.93/0.99  fof(f4,axiom,(
% 1.93/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f13,plain,(
% 1.93/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f4])).
% 1.93/0.99  
% 1.93/0.99  fof(f14,plain,(
% 1.93/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f13])).
% 1.93/0.99  
% 1.93/0.99  fof(f46,plain,(
% 1.93/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f14])).
% 1.93/0.99  
% 1.93/0.99  fof(f56,plain,(
% 1.93/0.99    ~v2_struct_0(sK3)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f48,plain,(
% 1.93/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f7,axiom,(
% 1.93/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f18,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(ennf_transformation,[],[f7])).
% 1.93/0.99  
% 1.93/0.99  fof(f19,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(flattening,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f31,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f19])).
% 1.93/0.99  
% 1.93/0.99  fof(f32,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(rectify,[],[f31])).
% 1.93/0.99  
% 1.93/0.99  fof(f33,plain,(
% 1.93/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f34,plain,(
% 1.93/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.93/0.99  
% 1.93/0.99  fof(f55,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f34])).
% 1.93/0.99  
% 1.93/0.99  fof(f53,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f34])).
% 1.93/0.99  
% 1.93/0.99  fof(f51,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f50,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f54,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f34])).
% 1.93/0.99  
% 1.93/0.99  fof(f62,plain,(
% 1.93/0.99    r2_lattice3(sK3,sK5,sK6) | r1_lattice3(sK3,sK5,sK6)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f61,plain,(
% 1.93/0.99    sK6 = sK7),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f52,plain,(
% 1.93/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f34])).
% 1.93/0.99  
% 1.93/0.99  fof(f59,plain,(
% 1.93/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f1,axiom,(
% 1.93/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f22,plain,(
% 1.93/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.93/0.99    inference(nnf_transformation,[],[f1])).
% 1.93/0.99  
% 1.93/0.99  fof(f23,plain,(
% 1.93/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.93/0.99    inference(rectify,[],[f22])).
% 1.93/0.99  
% 1.93/0.99  fof(f24,plain,(
% 1.93/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f25,plain,(
% 1.93/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.93/0.99  
% 1.93/0.99  fof(f41,plain,(
% 1.93/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f25])).
% 1.93/0.99  
% 1.93/0.99  fof(f43,plain,(
% 1.93/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f40,plain,(
% 1.93/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f25])).
% 1.93/0.99  
% 1.93/0.99  fof(f60,plain,(
% 1.93/0.99    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f44,plain,(
% 1.93/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f63,plain,(
% 1.93/0.99    r2_lattice3(sK3,sK5,sK6) | ~r1_lattice3(sK4,sK5,sK7)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f64,plain,(
% 1.93/0.99    ~r2_lattice3(sK4,sK5,sK7) | r1_lattice3(sK3,sK5,sK6)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f58,plain,(
% 1.93/0.99    ~v2_struct_0(sK4)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  fof(f45,plain,(
% 1.93/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f65,plain,(
% 1.93/0.99    ~r2_lattice3(sK4,sK5,sK7) | ~r1_lattice3(sK4,sK5,sK7)),
% 1.93/0.99    inference(cnf_transformation,[],[f39])).
% 1.93/0.99  
% 1.93/0.99  cnf(c_253,plain,
% 1.93/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_252,plain,
% 1.93/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2675,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_10,plain,
% 1.93/0.99      ( r1_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_24,negated_conjecture,
% 1.93/0.99      ( l1_orders_2(sK3) ),
% 1.93/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_413,plain,
% 1.93/0.99      ( r1_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_414,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2655,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | m1_subset_1(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_414]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3121,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2655]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2670,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0_46,X1_46)
% 1.93/0.99      | r2_hidden(X0_46,X1_46)
% 1.93/0.99      | v1_xboole_0(X1_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3107,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 1.93/0.99      | r2_hidden(X0_46,X1_46) = iProver_top
% 1.93/0.99      | v1_xboole_0(X1_46) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2670]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4333,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_3107]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_27,plain,
% 1.93/0.99      ( l1_orders_2(sK3) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_7,plain,
% 1.93/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6,plain,
% 1.93/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_282,plain,
% 1.93/0.99      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.93/0.99      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_25,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK3) ),
% 1.93/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_310,plain,
% 1.93/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_282,c_25]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_311,plain,
% 1.93/0.99      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_312,plain,
% 1.93/0.99      ( l1_orders_2(sK3) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4745,plain,
% 1.93/0.99      ( r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,X1_46) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4333,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4746,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK1(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_4745]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_11,plain,
% 1.93/0.99      ( r1_orders_2(X0,X1,X2)
% 1.93/0.99      | ~ r1_lattice3(X0,X3,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | ~ r2_hidden(X2,X3)
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_392,plain,
% 1.93/0.99      ( r1_orders_2(X0,X1,X2)
% 1.93/0.99      | ~ r1_lattice3(X0,X3,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | ~ r2_hidden(X2,X3)
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_393,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0,X1)
% 1.93/0.99      | ~ r1_lattice3(sK3,X2,X0)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(X1,X2) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2656,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ r1_lattice3(sK3,X2_46,X0_46)
% 1.93/0.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(X1_46,X2_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_393]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3120,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X2_46,X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(X1_46,X2_46) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2656]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4332,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X3_46,X0_46) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK1(sK3,X1_46,X2_46),X3_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_3120]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5746,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_4746,c_4332]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_12,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_377,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_378,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0,X1)
% 1.93/0.99      | ~ r1_orders_2(sK3,sK2(sK3,X0,X1),X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_377]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2657,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_378]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3119,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),X1_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2657]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6177,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46)),u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(sK3,X1_46,X2_46),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5746,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_14,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_347,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_348,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0,X1),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_347]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2659,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_348]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3117,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2659]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6276,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(forward_subsumption_resolution,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_6177,c_3121,c_3117]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4243,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_3107]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4733,plain,
% 1.93/0.99      ( r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X0_46,X1_46) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4243,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4734,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_4733]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4242,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X3_46,X2_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),X3_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_3120]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5626,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X2_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_4734,c_4242]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6125,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5626,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2715,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2659]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6257,plain,
% 1.93/0.99      ( m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6125,c_2715]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6258,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_6257]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_8,plain,
% 1.93/0.99      ( ~ r1_orders_2(X0,X1,sK1(X0,X2,X1))
% 1.93/0.99      | r1_lattice3(X0,X2,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_443,plain,
% 1.93/0.99      ( ~ r1_orders_2(X0,X1,sK1(X0,X2,X1))
% 1.93/0.99      | r1_lattice3(X0,X2,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_444,plain,
% 1.93/0.99      ( ~ r1_orders_2(sK3,X0,sK1(sK3,X1,X0))
% 1.93/0.99      | r1_lattice3(sK3,X1,X0)
% 1.93/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_443]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2653,plain,
% 1.93/0.99      ( ~ r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X0_46))
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46)
% 1.93/0.99      | ~ m1_subset_1(X0_46,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_444]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3123,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X0_46)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2653]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6176,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X1_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5746,c_3123]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_9,plain,
% 1.93/0.99      ( r1_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_428,plain,
% 1.93/0.99      ( r1_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_429,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | r2_hidden(sK1(sK3,X0,X1),X0) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2654,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | r2_hidden(sK1(sK3,X0_46,X1_46),X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_429]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3122,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK1(sK3,X0_46,X1_46),X0_46) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2654]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5745,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3122,c_4332]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5801,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46)),u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(sK3,X1_46,X2_46),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5745,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6114,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,sK2(sK3,X0_46,sK1(sK3,X1_46,X2_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(forward_subsumption_resolution,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_5801,c_3121,c_3117]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_13,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_362,plain,
% 1.93/0.99      ( r2_lattice3(X0,X1,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_363,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0,X1)
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | r2_hidden(sK2(sK3,X0,X1),X0) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2658,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_363]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3118,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),X0_46) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2658]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5625,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,X2_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3118,c_4242]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5734,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5625,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5820,plain,
% 1.93/0.99      ( m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5734,c_2715]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5821,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46))) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X2_46,sK2(sK3,X0_46,X1_46)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5820]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_19,negated_conjecture,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) | r1_lattice3(sK3,sK5,sK6) ),
% 1.93/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2666,negated_conjecture,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) | r1_lattice3(sK3,sK5,sK6) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3111,plain,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK6) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2666]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_20,negated_conjecture,
% 1.93/0.99      ( sK6 = sK7 ),
% 1.93/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2665,negated_conjecture,
% 1.93/0.99      ( sK6 = sK7 ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3150,plain,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_3111,c_2665]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_15,plain,
% 1.93/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.93/0.99      | r1_orders_2(X0,X3,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ r2_hidden(X3,X1)
% 1.93/0.99      | ~ l1_orders_2(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_326,plain,
% 1.93/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 1.93/0.99      | r1_orders_2(X0,X3,X2)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ r2_hidden(X3,X1)
% 1.93/0.99      | sK3 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_327,plain,
% 1.93/0.99      ( ~ r2_lattice3(sK3,X0,X1)
% 1.93/0.99      | r1_orders_2(sK3,X2,X1)
% 1.93/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(X2,X0) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_326]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2660,plain,
% 1.93/0.99      ( ~ r2_lattice3(sK3,X0_46,X1_46)
% 1.93/0.99      | r1_orders_2(sK3,X2_46,X1_46)
% 1.93/0.99      | ~ m1_subset_1(X1_46,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(X2_46,u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(X2_46,X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_327]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3116,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) != iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X2_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(X2_46,X0_46) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2660]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3782,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(X0_46,sK5) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3150,c_3116]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_22,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2663,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3113,plain,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2663]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3129,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_3113,c_2665]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4373,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(X0_46,sK5) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3782,c_3129]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4374,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(X0_46,sK5) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_4373]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4385,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,X1_46),sK5) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_4374]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5461,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_4385,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5464,plain,
% 1.93/0.99      ( r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5461,c_3129]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5465,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK2(sK3,X0_46,sK7),sK5) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5464]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_0,plain,
% 1.93/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2674,plain,
% 1.93/0.99      ( r2_hidden(sK0(X0_46),X0_46) | v1_xboole_0(X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3103,plain,
% 1.93/0.99      ( r2_hidden(sK0(X0_46),X0_46) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2674]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4,plain,
% 1.93/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1,plain,
% 1.93/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_152,plain,
% 1.93/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4,c_1]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_153,plain,
% 1.93/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_152]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2662,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46) | ~ r2_hidden(X0_46,X1_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_153]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3114,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_hidden(X0_46,X1_46) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2662]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3935,plain,
% 1.93/0.99      ( m1_subset_1(sK0(X0_46),X0_46) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3103,c_3114]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4029,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3935,c_3120]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5174,plain,
% 1.93/0.99      ( r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4029,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5175,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK0(u1_struct_0(sK3)),X1_46) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5174]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5184,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3103,c_5175]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5220,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
% 1.93/0.99      | r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_5184,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5221,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5220]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5229,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK0(u1_struct_0(sK3)))) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_5221,c_3119]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3399,plain,
% 1.93/0.99      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2674]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3400,plain,
% 1.93/0.99      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3399]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3336,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(X0_46,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2662]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3496,plain,
% 1.93/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
% 1.93/0.99      | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3336]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3497,plain,
% 1.93/0.99      ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3496]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3662,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3)))
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2659]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3668,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3662]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5358,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,u1_struct_0(sK3),sK2(sK3,X0_46,sK0(u1_struct_0(sK3)))) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_5229,c_27,c_312,c_3400,c_3497,c_3668]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2673,plain,
% 1.93/0.99      ( ~ r2_hidden(X0_46,X1_46) | ~ v1_xboole_0(X1_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3104,plain,
% 1.93/0.99      ( r2_hidden(X0_46,X1_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(X1_46) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2673]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4222,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3122,c_3104]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4634,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3935,c_4222]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5306,plain,
% 1.93/0.99      ( v1_xboole_0(X0_46) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4634,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5307,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5306]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4170,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3118,c_3104]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4503,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3935,c_4170]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5296,plain,
% 1.93/0.99      ( v1_xboole_0(X0_46) != iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4503,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5297,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5296]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4387,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3935,c_4374]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5046,plain,
% 1.93/0.99      ( r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4387,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5047,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK0(u1_struct_0(sK3)),sK5) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_5046]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4632,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X2_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_4222]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4631,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X2_46,sK1(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X2_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_4222]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4630,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_4222]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3869,plain,
% 1.93/0.99      ( r1_orders_2(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X0_46) != iProver_top
% 1.93/0.99      | m1_subset_1(X0_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X1_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_3120]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4028,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X0_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3935,c_3869]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4580,plain,
% 1.93/0.99      ( r2_hidden(sK7,X0_46) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
% 1.93/0.99      | r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_4028,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4581,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK0(u1_struct_0(sK3)),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK0(u1_struct_0(sK3))) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X0_46) != iProver_top ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_4580]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4501,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r2_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X2_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_4170]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4500,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK1(sK3,X1_46,X2_46)) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X1_46,X2_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X2_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_4170]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4499,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,sK7) = iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_4170]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4383,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK7,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK7,sK5) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_4374]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3887,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK7,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,sK7) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X0_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_3869]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3896,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK7,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,sK5) != iProver_top ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3887]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4489,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK7,sK7) = iProver_top
% 1.93/0.99      | r2_hidden(sK7,sK5) != iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4383,c_3896]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4384,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK1(sK3,X0_46,X1_46),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK1(sK3,X0_46,X1_46),sK5) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_4374]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4331,plain,
% 1.93/0.99      ( r1_orders_2(sK3,sK1(sK3,X0_46,X1_46),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X2_46,sK1(sK3,X0_46,X1_46)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X2_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3121,c_3869]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4241,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | r1_orders_2(sK3,sK2(sK3,X0_46,X1_46),sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK3,X2_46,sK2(sK3,X0_46,X1_46)) != iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | r2_hidden(sK7,X2_46) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3117,c_3869]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4221,plain,
% 1.93/0.99      ( r1_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK1(sK3,X0_46,X1_46),X0_46) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3122,c_3114]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4169,plain,
% 1.93/0.99      ( r2_lattice3(sK3,X0_46,X1_46) = iProver_top
% 1.93/0.99      | m1_subset_1(X1_46,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK2(sK3,X0_46,X1_46),X0_46) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3118,c_3114]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3597,plain,
% 1.93/0.99      ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3129,c_3107]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4158,plain,
% 1.93/0.99      ( r2_hidden(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3597,c_27,c_312]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_21,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2664,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3112,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2664]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3596,plain,
% 1.93/0.99      ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
% 1.93/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3112,c_3107]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2671,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0_46,X1_46)
% 1.93/0.99      | ~ v1_xboole_0(X1_46)
% 1.93/0.99      | v1_xboole_0(X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3106,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(X1_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2671]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3549,plain,
% 1.93/0.99      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_3112,c_3106]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_18,negated_conjecture,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) | ~ r1_lattice3(sK4,sK5,sK7) ),
% 1.93/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2667,negated_conjecture,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) | ~ r1_lattice3(sK4,sK5,sK7) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3110,plain,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2667]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3160,plain,
% 1.93/0.99      ( r2_lattice3(sK3,sK5,sK7) = iProver_top
% 1.93/0.99      | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_3110,c_2665]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_17,negated_conjecture,
% 1.93/0.99      ( ~ r2_lattice3(sK4,sK5,sK7) | r1_lattice3(sK3,sK5,sK6) ),
% 1.93/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2668,negated_conjecture,
% 1.93/0.99      ( ~ r2_lattice3(sK4,sK5,sK7) | r1_lattice3(sK3,sK5,sK6) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3109,plain,
% 1.93/0.99      ( r2_lattice3(sK4,sK5,sK7) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK6) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2668]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3155,plain,
% 1.93/0.99      ( r2_lattice3(sK4,sK5,sK7) != iProver_top
% 1.93/0.99      | r1_lattice3(sK3,sK5,sK7) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_3109,c_2665]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_23,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK4) ),
% 1.93/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_300,plain,
% 1.93/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_282,c_23]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_301,plain,
% 1.93/0.99      ( ~ l1_orders_2(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_300]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_458,plain,
% 1.93/0.99      ( ~ v1_xboole_0(u1_struct_0(sK4)) | sK3 != sK4 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_301]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2652,plain,
% 1.93/0.99      ( ~ v1_xboole_0(u1_struct_0(sK4)) | sK3 != sK4 ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_458]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3124,plain,
% 1.93/0.99      ( sK3 != sK4 | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2652]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2,plain,
% 1.93/0.99      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2672,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46)
% 1.93/0.99      | ~ v1_xboole_0(X1_46)
% 1.93/0.99      | ~ v1_xboole_0(X0_46) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3105,plain,
% 1.93/0.99      ( m1_subset_1(X0_46,X1_46) = iProver_top
% 1.93/0.99      | v1_xboole_0(X1_46) != iProver_top
% 1.93/0.99      | v1_xboole_0(X0_46) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2672]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_313,plain,
% 1.93/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.93/0.99      inference(global_propositional_subsumption,[status(thm)],[c_311,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2661,plain,
% 1.93/0.99      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_313]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3115,plain,
% 1.93/0.99      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_16,negated_conjecture,
% 1.93/0.99      ( ~ r2_lattice3(sK4,sK5,sK7) | ~ r1_lattice3(sK4,sK5,sK7) ),
% 1.93/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2669,negated_conjecture,
% 1.93/0.99      ( ~ r2_lattice3(sK4,sK5,sK7) | ~ r1_lattice3(sK4,sK5,sK7) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3108,plain,
% 1.93/0.99      ( r2_lattice3(sK4,sK5,sK7) != iProver_top
% 1.93/0.99      | r1_lattice3(sK4,sK5,sK7) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2669]) ).
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS output end Saturation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  ------                               Statistics
% 1.93/0.99  
% 1.93/0.99  ------ General
% 1.93/0.99  
% 1.93/0.99  abstr_ref_over_cycles:                  0
% 1.93/0.99  abstr_ref_under_cycles:                 0
% 1.93/0.99  gc_basic_clause_elim:                   0
% 1.93/0.99  forced_gc_time:                         0
% 1.93/0.99  parsing_time:                           0.009
% 1.93/0.99  unif_index_cands_time:                  0.
% 1.93/0.99  unif_index_add_time:                    0.
% 1.93/0.99  orderings_time:                         0.
% 1.93/0.99  out_proof_time:                         0.
% 1.93/0.99  total_time:                             0.179
% 1.93/0.99  num_of_symbols:                         48
% 1.93/0.99  num_of_terms:                           3198
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing
% 1.93/0.99  
% 1.93/0.99  num_of_splits:                          0
% 1.93/0.99  num_of_split_atoms:                     0
% 1.93/0.99  num_of_reused_defs:                     0
% 1.93/0.99  num_eq_ax_congr_red:                    22
% 1.93/0.99  num_of_sem_filtered_clauses:            1
% 1.93/0.99  num_of_subtypes:                        2
% 1.93/0.99  monotx_restored_types:                  0
% 1.93/0.99  sat_num_of_epr_types:                   0
% 1.93/0.99  sat_num_of_non_cyclic_types:            0
% 1.93/0.99  sat_guarded_non_collapsed_types:        0
% 1.93/0.99  num_pure_diseq_elim:                    0
% 1.93/0.99  simp_replaced_by:                       0
% 1.93/0.99  res_preprocessed:                       122
% 1.93/0.99  prep_upred:                             0
% 1.93/0.99  prep_unflattend:                        158
% 1.93/0.99  smt_new_axioms:                         0
% 1.93/0.99  pred_elim_cands:                        6
% 1.93/0.99  pred_elim:                              3
% 1.93/0.99  pred_elim_cl:                           3
% 1.93/0.99  pred_elim_cycles:                       11
% 1.93/0.99  merged_defs:                            0
% 1.93/0.99  merged_defs_ncl:                        0
% 1.93/0.99  bin_hyper_res:                          0
% 1.93/0.99  prep_cycles:                            4
% 1.93/0.99  pred_elim_time:                         0.035
% 1.93/0.99  splitting_time:                         0.
% 1.93/0.99  sem_filter_time:                        0.
% 1.93/0.99  monotx_time:                            0.
% 1.93/0.99  subtype_inf_time:                       0.
% 1.93/0.99  
% 1.93/0.99  ------ Problem properties
% 1.93/0.99  
% 1.93/0.99  clauses:                                23
% 1.93/0.99  conjectures:                            7
% 1.93/0.99  epr:                                    10
% 1.93/0.99  horn:                                   16
% 1.93/0.99  ground:                                 9
% 1.93/0.99  unary:                                  4
% 1.93/0.99  binary:                                 8
% 1.93/0.99  lits:                                   57
% 1.93/0.99  lits_eq:                                2
% 1.93/0.99  fd_pure:                                0
% 1.93/0.99  fd_pseudo:                              0
% 1.93/0.99  fd_cond:                                0
% 1.93/0.99  fd_pseudo_cond:                         0
% 1.93/0.99  ac_symbols:                             0
% 1.93/0.99  
% 1.93/0.99  ------ Propositional Solver
% 1.93/0.99  
% 1.93/0.99  prop_solver_calls:                      28
% 1.93/0.99  prop_fast_solver_calls:                 1565
% 1.93/0.99  smt_solver_calls:                       0
% 1.93/0.99  smt_fast_solver_calls:                  0
% 1.93/0.99  prop_num_of_clauses:                    1649
% 1.93/0.99  prop_preprocess_simplified:             5606
% 1.93/0.99  prop_fo_subsumed:                       60
% 1.93/0.99  prop_solver_time:                       0.
% 1.93/0.99  smt_solver_time:                        0.
% 1.93/0.99  smt_fast_solver_time:                   0.
% 1.93/0.99  prop_fast_solver_time:                  0.
% 1.93/0.99  prop_unsat_core_time:                   0.
% 1.93/0.99  
% 1.93/0.99  ------ QBF
% 1.93/0.99  
% 1.93/0.99  qbf_q_res:                              0
% 1.93/0.99  qbf_num_tautologies:                    0
% 1.93/0.99  qbf_prep_cycles:                        0
% 1.93/0.99  
% 1.93/0.99  ------ BMC1
% 1.93/0.99  
% 1.93/0.99  bmc1_current_bound:                     -1
% 1.93/0.99  bmc1_last_solved_bound:                 -1
% 1.93/0.99  bmc1_unsat_core_size:                   -1
% 1.93/0.99  bmc1_unsat_core_parents_size:           -1
% 1.93/0.99  bmc1_merge_next_fun:                    0
% 1.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation
% 1.93/0.99  
% 1.93/0.99  inst_num_of_clauses:                    403
% 1.93/0.99  inst_num_in_passive:                    15
% 1.93/0.99  inst_num_in_active:                     297
% 1.93/0.99  inst_num_in_unprocessed:                91
% 1.93/0.99  inst_num_of_loops:                      340
% 1.93/0.99  inst_num_of_learning_restarts:          0
% 1.93/0.99  inst_num_moves_active_passive:          38
% 1.93/0.99  inst_lit_activity:                      0
% 1.93/0.99  inst_lit_activity_moves:                0
% 1.93/0.99  inst_num_tautologies:                   0
% 1.93/0.99  inst_num_prop_implied:                  0
% 1.93/0.99  inst_num_existing_simplified:           0
% 1.93/0.99  inst_num_eq_res_simplified:             0
% 1.93/0.99  inst_num_child_elim:                    0
% 1.93/0.99  inst_num_of_dismatching_blockings:      83
% 1.93/0.99  inst_num_of_non_proper_insts:           515
% 1.93/0.99  inst_num_of_duplicates:                 0
% 1.93/0.99  inst_inst_num_from_inst_to_res:         0
% 1.93/0.99  inst_dismatching_checking_time:         0.
% 1.93/0.99  
% 1.93/0.99  ------ Resolution
% 1.93/0.99  
% 1.93/0.99  res_num_of_clauses:                     0
% 1.93/0.99  res_num_in_passive:                     0
% 1.93/0.99  res_num_in_active:                      0
% 1.93/0.99  res_num_of_loops:                       126
% 1.93/0.99  res_forward_subset_subsumed:            78
% 1.93/0.99  res_backward_subset_subsumed:           0
% 1.93/0.99  res_forward_subsumed:                   8
% 1.93/0.99  res_backward_subsumed:                  0
% 1.93/0.99  res_forward_subsumption_resolution:     6
% 1.93/0.99  res_backward_subsumption_resolution:    0
% 1.93/0.99  res_clause_to_clause_subsumption:       491
% 1.93/0.99  res_orphan_elimination:                 0
% 1.93/0.99  res_tautology_del:                      68
% 1.93/0.99  res_num_eq_res_simplified:              0
% 1.93/0.99  res_num_sel_changes:                    0
% 1.93/0.99  res_moves_from_active_to_pass:          0
% 1.93/0.99  
% 1.93/0.99  ------ Superposition
% 1.93/0.99  
% 1.93/0.99  sup_time_total:                         0.
% 1.93/0.99  sup_time_generating:                    0.
% 1.93/0.99  sup_time_sim_full:                      0.
% 1.93/0.99  sup_time_sim_immed:                     0.
% 1.93/0.99  
% 1.93/0.99  sup_num_of_clauses:                     77
% 1.93/0.99  sup_num_in_active:                      66
% 1.93/0.99  sup_num_in_passive:                     11
% 1.93/0.99  sup_num_of_loops:                       66
% 1.93/0.99  sup_fw_superposition:                   45
% 1.93/0.99  sup_bw_superposition:                   52
% 1.93/0.99  sup_immediate_simplified:               33
% 1.93/0.99  sup_given_eliminated:                   0
% 1.93/0.99  comparisons_done:                       0
% 1.93/0.99  comparisons_avoided:                    0
% 1.93/0.99  
% 1.93/0.99  ------ Simplifications
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  sim_fw_subset_subsumed:                 25
% 1.93/0.99  sim_bw_subset_subsumed:                 0
% 1.93/0.99  sim_fw_subsumed:                        18
% 1.93/0.99  sim_bw_subsumed:                        0
% 1.93/0.99  sim_fw_subsumption_res:                 4
% 1.93/0.99  sim_bw_subsumption_res:                 0
% 1.93/0.99  sim_tautology_del:                      6
% 1.93/0.99  sim_eq_tautology_del:                   0
% 1.93/0.99  sim_eq_res_simp:                        0
% 1.93/0.99  sim_fw_demodulated:                     0
% 1.93/0.99  sim_bw_demodulated:                     0
% 1.93/0.99  sim_light_normalised:                   4
% 1.93/0.99  sim_joinable_taut:                      0
% 1.93/0.99  sim_joinable_simp:                      0
% 1.93/0.99  sim_ac_normalised:                      0
% 1.93/0.99  sim_smt_subsumption:                    0
% 1.93/0.99  
%------------------------------------------------------------------------------
