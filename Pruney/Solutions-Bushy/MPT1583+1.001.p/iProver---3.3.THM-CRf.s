%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1583+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:57 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  230 (1375 expanded)
%              Number of clauses        :  160 ( 367 expanded)
%              Number of leaves         :   21 ( 453 expanded)
%              Depth                    :   18
%              Number of atoms          :  960 (12603 expanded)
%              Number of equality atoms :  239 (1306 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f13])).

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
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
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
        & m1_yellow_0(sK3,X0)
        & v4_yellow_0(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
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
          & m1_yellow_0(X1,sK2)
          & v4_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ( ~ r2_lattice3(sK3,sK4,sK6)
        & r2_lattice3(sK2,sK4,sK5) )
      | ( ~ r1_lattice3(sK3,sK4,sK6)
        & r1_lattice3(sK2,sK4,sK5) ) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_yellow_0(sK3,sK2)
    & v4_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f28,f40,f39,f38,f37])).

fof(f61,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

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
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f60,plain,(
    v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_377,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_378,plain,
    ( ~ l1_orders_2(sK2)
    | l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_25,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_380,plain,
    ( l1_orders_2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_25])).

cnf(c_670,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_380])).

cnf(c_671,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_3192,plain,
    ( r1_lattice3(sK3,X0_49,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_671])).

cnf(c_3756,plain,
    ( r1_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3192])).

cnf(c_13,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_360,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_26,c_25,c_24])).

cnf(c_365,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_3209,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_365])).

cnf(c_3739,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3209])).

cnf(c_6077,plain,
    ( r1_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_3739])).

cnf(c_6150,plain,
    ( r1_lattice3(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6077])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_604,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_380])).

cnf(c_605,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_3196,plain,
    ( r2_lattice3(sK3,X0_49,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0_49,X0_48),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_3752,plain,
    ( r2_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49,X0_48),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3196])).

cnf(c_5386,plain,
    ( r2_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49,X0_48),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_3739])).

cnf(c_5431,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5386])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_279,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_395,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_24])).

cnf(c_396,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_25,c_378])).

cnf(c_433,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_398])).

cnf(c_434,plain,
    ( r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_3206,plain,
    ( r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_434])).

cnf(c_3742,plain,
    ( r2_hidden(X0_48,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_5385,plain,
    ( r2_lattice3(sK3,X0_49,X0_48) = iProver_top
    | r2_hidden(sK1(sK3,X0_49,X0_48),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_3742])).

cnf(c_5428,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5385])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_451,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_452,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_3205,plain,
    ( ~ r2_lattice3(sK2,X0_49,X0_48)
    | r1_orders_2(sK2,X1_48,X0_48)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_5234,plain,
    ( ~ r2_lattice3(sK2,X0_49,X0_48)
    | r1_orders_2(sK2,sK1(sK3,X0_49,X1_48),X0_48)
    | ~ r2_hidden(sK1(sK3,X0_49,X1_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK3,X0_49,X1_48),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_5240,plain,
    ( r2_lattice3(sK2,X0_49,X0_48) != iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0_49,X1_48),X0_48) = iProver_top
    | r2_hidden(sK1(sK3,X0_49,X1_48),X0_49) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49,X1_48),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5234])).

cnf(c_5242,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_orders_2(sK2,sK1(sK3,sK4,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK3,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5240])).

cnf(c_14,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ m1_yellow_0(X3,X0)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( v4_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_319,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_0(X3,X0)
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | sK2 != X0
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_320,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK3,X0,X1)
    | ~ m1_yellow_0(sK3,sK2)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_25,c_22])).

cnf(c_325,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_344,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_325,c_11])).

cnf(c_389,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK3,X0,X1)
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_365,c_344])).

cnf(c_3208,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | r1_orders_2(sK3,X0_48,X1_48)
    | ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_5221,plain,
    ( ~ r1_orders_2(sK2,sK1(sK3,X0_49,X0_48),X0_48)
    | r1_orders_2(sK3,sK1(sK3,X0_49,X0_48),X0_48)
    | ~ r2_hidden(sK1(sK3,X0_49,X0_48),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,X0_49,X0_48),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3208])).

cnf(c_5222,plain,
    ( r1_orders_2(sK2,sK1(sK3,X0_49,X0_48),X0_48) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0_49,X0_48),X0_48) = iProver_top
    | r2_hidden(sK1(sK3,X0_49,X0_48),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_49,X0_48),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5221])).

cnf(c_5224,plain,
    ( r1_orders_2(sK2,sK1(sK3,sK4,sK5),sK5) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,sK4,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_517,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_518,plain,
    ( r1_orders_2(sK2,X0,X1)
    | ~ r1_lattice3(sK2,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_3201,plain,
    ( r1_orders_2(sK2,X0_48,X1_48)
    | ~ r1_lattice3(sK2,X0_49,X0_48)
    | ~ r2_hidden(X1_48,X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_5104,plain,
    ( r1_orders_2(sK2,X0_48,sK0(sK3,X0_49,X1_48))
    | ~ r1_lattice3(sK2,X0_49,X0_48)
    | ~ r2_hidden(sK0(sK3,X0_49,X1_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3,X0_49,X1_48),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3201])).

cnf(c_5105,plain,
    ( r1_orders_2(sK2,X0_48,sK0(sK3,X0_49,X1_48)) = iProver_top
    | r1_lattice3(sK2,X0_49,X0_48) != iProver_top
    | r2_hidden(sK0(sK3,X0_49,X1_48),X0_49) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,X1_48),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5104])).

cnf(c_5107,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK3,sK4,sK5)) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_hidden(sK0(sK3,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5105])).

cnf(c_5090,plain,
    ( ~ r1_orders_2(sK2,X0_48,sK0(sK3,X0_49,X0_48))
    | r1_orders_2(sK3,X0_48,sK0(sK3,X0_49,X0_48))
    | ~ r2_hidden(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3208])).

cnf(c_5091,plain,
    ( r1_orders_2(sK2,X0_48,sK0(sK3,X0_49,X0_48)) != iProver_top
    | r1_orders_2(sK3,X0_48,sK0(sK3,X0_49,X0_48)) = iProver_top
    | r2_hidden(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5090])).

cnf(c_5093,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK3,sK4,sK5)) != iProver_top
    | r1_orders_2(sK3,sK5,sK0(sK3,sK4,sK5)) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5091])).

cnf(c_4114,plain,
    ( r1_orders_2(sK2,X0_48,sK0(sK3,X0_49,sK6))
    | ~ r1_lattice3(sK2,X0_49,X0_48)
    | ~ r2_hidden(sK0(sK3,X0_49,sK6),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3201])).

cnf(c_5039,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK3,X0_49,sK6))
    | ~ r1_lattice3(sK2,X0_49,sK6)
    | ~ r2_hidden(sK0(sK3,X0_49,sK6),X0_49)
    | ~ m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4114])).

cnf(c_5040,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK3,X0_49,sK6)) = iProver_top
    | r1_lattice3(sK2,X0_49,sK6) != iProver_top
    | r2_hidden(sK0(sK3,X0_49,sK6),X0_49) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5039])).

cnf(c_5042,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK3,sK4,sK6)) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) != iProver_top
    | r2_hidden(sK0(sK3,sK4,sK6),sK4) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK6),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5040])).

cnf(c_3219,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_4554,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_3219])).

cnf(c_3220,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_4203,plain,
    ( X0_48 != X1_48
    | sK6 != X1_48
    | sK6 = X0_48 ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_4553,plain,
    ( X0_48 != sK6
    | sK6 = X0_48
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_4555,plain,
    ( sK5 != sK6
    | sK6 = sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4553])).

cnf(c_4081,plain,
    ( ~ r1_orders_2(sK2,sK6,X0_48)
    | r1_orders_2(sK3,sK6,X0_48)
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3208])).

cnf(c_4529,plain,
    ( ~ r1_orders_2(sK2,sK6,sK0(sK3,X0_49,sK6))
    | r1_orders_2(sK3,sK6,sK0(sK3,X0_49,sK6))
    | ~ r2_hidden(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4081])).

cnf(c_4530,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK3,X0_49,sK6)) != iProver_top
    | r1_orders_2(sK3,sK6,sK0(sK3,X0_49,sK6)) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4529])).

cnf(c_4532,plain,
    ( r1_orders_2(sK2,sK6,sK0(sK3,sK4,sK6)) != iProver_top
    | r1_orders_2(sK3,sK6,sK0(sK3,sK4,sK6)) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK6),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4530])).

cnf(c_4442,plain,
    ( m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3209])).

cnf(c_4443,plain,
    ( m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4442])).

cnf(c_4445,plain,
    ( m1_subset_1(sK0(sK3,sK4,sK6),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4443])).

cnf(c_3221,plain,
    ( ~ r1_lattice3(X0_47,X0_49,X0_48)
    | r1_lattice3(X0_47,X0_49,X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4097,plain,
    ( ~ r1_lattice3(sK3,sK4,X0_48)
    | r1_lattice3(sK3,sK4,sK6)
    | sK6 != X0_48 ),
    inference(instantiation,[status(thm)],[c_3221])).

cnf(c_4098,plain,
    ( sK6 != X0_48
    | r1_lattice3(sK3,sK4,X0_48) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4097])).

cnf(c_4100,plain,
    ( sK6 != sK5
    | r1_lattice3(sK3,sK4,sK5) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4098])).

cnf(c_3225,plain,
    ( ~ r2_lattice3(X0_47,X0_49,X0_48)
    | r2_lattice3(X0_47,X0_49,X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4066,plain,
    ( ~ r2_lattice3(sK3,sK4,X0_48)
    | r2_lattice3(sK3,sK4,sK6)
    | sK6 != X0_48 ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_4067,plain,
    ( sK6 != X0_48
    | r2_lattice3(sK3,sK4,X0_48) != iProver_top
    | r2_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4066])).

cnf(c_4069,plain,
    ( sK6 != sK5
    | r2_lattice3(sK3,sK4,sK5) != iProver_top
    | r2_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4067])).

cnf(c_3223,plain,
    ( ~ m1_subset_1(X0_48,X0_49)
    | m1_subset_1(X1_48,X0_49)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4033,plain,
    ( m1_subset_1(X0_48,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | X0_48 != sK6 ),
    inference(instantiation,[status(thm)],[c_3223])).

cnf(c_4034,plain,
    ( X0_48 != sK6
    | m1_subset_1(X0_48,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4033])).

cnf(c_4036,plain,
    ( sK5 != sK6
    | m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4034])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_685,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_380])).

cnf(c_686,plain,
    ( r1_lattice3(sK3,X0,X1)
    | r2_hidden(sK0(sK3,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_3191,plain,
    ( r1_lattice3(sK3,X0_49,X0_48)
    | r2_hidden(sK0(sK3,X0_49,X0_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_686])).

cnf(c_4018,plain,
    ( r1_lattice3(sK3,X0_49,sK6)
    | r2_hidden(sK0(sK3,X0_49,sK6),X0_49)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3191])).

cnf(c_4019,plain,
    ( r1_lattice3(sK3,X0_49,sK6) = iProver_top
    | r2_hidden(sK0(sK3,X0_49,sK6),X0_49) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4018])).

cnf(c_4021,plain,
    ( r1_lattice3(sK3,sK4,sK6) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK6),sK4) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_700,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_380])).

cnf(c_701,plain,
    ( ~ r1_orders_2(sK3,X0,sK0(sK3,X1,X0))
    | r1_lattice3(sK3,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_3190,plain,
    ( ~ r1_orders_2(sK3,X0_48,sK0(sK3,X0_49,X0_48))
    | r1_lattice3(sK3,X0_49,X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_701])).

cnf(c_4013,plain,
    ( ~ r1_orders_2(sK3,sK6,sK0(sK3,X0_49,sK6))
    | r1_lattice3(sK3,X0_49,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_4014,plain,
    ( r1_orders_2(sK3,sK6,sK0(sK3,X0_49,sK6)) != iProver_top
    | r1_lattice3(sK3,X0_49,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4013])).

cnf(c_4016,plain,
    ( r1_orders_2(sK3,sK6,sK0(sK3,sK4,sK6)) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4014])).

cnf(c_3998,plain,
    ( r1_lattice3(sK3,X0_49,sK6)
    | m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3192])).

cnf(c_3999,plain,
    ( r1_lattice3(sK3,X0_49,sK6) = iProver_top
    | m1_subset_1(sK0(sK3,X0_49,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3998])).

cnf(c_4001,plain,
    ( r1_lattice3(sK3,sK4,sK6) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK6),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3999])).

cnf(c_3985,plain,
    ( r2_hidden(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3206])).

cnf(c_3986,plain,
    ( r2_hidden(sK6,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3985])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3210,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3738,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3210])).

cnf(c_19,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3212,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3763,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3738,c_3212])).

cnf(c_16,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3215,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3734,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_3775,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3734,c_3212])).

cnf(c_3297,plain,
    ( r1_orders_2(sK3,X0_48,sK0(sK3,X0_49,X0_48)) != iProver_top
    | r1_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3190])).

cnf(c_3299,plain,
    ( r1_orders_2(sK3,sK5,sK0(sK3,sK4,sK5)) != iProver_top
    | r1_lattice3(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3297])).

cnf(c_3294,plain,
    ( r1_lattice3(sK3,X0_49,X0_48) = iProver_top
    | r2_hidden(sK0(sK3,X0_49,X0_48),X0_49) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3191])).

cnf(c_3296,plain,
    ( r1_lattice3(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK3,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3294])).

cnf(c_3291,plain,
    ( r1_lattice3(sK3,X0_49,X0_48) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0_49,X0_48),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3192])).

cnf(c_3293,plain,
    ( r1_lattice3(sK3,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK3,sK4,sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_634,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_380])).

cnf(c_635,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_3194,plain,
    ( r2_lattice3(sK3,X0_49,X0_48)
    | ~ r1_orders_2(sK3,sK1(sK3,X0_49,X0_48),X0_48)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_635])).

cnf(c_3285,plain,
    ( r2_lattice3(sK3,X0_49,X0_48) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0_49,X0_48),X0_48) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3194])).

cnf(c_3287,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,sK4,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3285])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_619,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_380])).

cnf(c_620,plain,
    ( r2_lattice3(sK3,X0,X1)
    | r2_hidden(sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_3195,plain,
    ( r2_lattice3(sK3,X0_49,X0_48)
    | r2_hidden(sK1(sK3,X0_49,X0_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_620])).

cnf(c_3282,plain,
    ( r2_lattice3(sK3,X0_49,X0_48) = iProver_top
    | r2_hidden(sK1(sK3,X0_49,X0_48),X0_49) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3195])).

cnf(c_3284,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | r2_hidden(sK1(sK3,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3282])).

cnf(c_3249,plain,
    ( r2_hidden(X0_48,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_48,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_3251,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3249])).

cnf(c_15,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6150,c_5431,c_5428,c_5242,c_5224,c_5107,c_5093,c_5042,c_4554,c_4555,c_4532,c_4445,c_4100,c_4069,c_4036,c_4021,c_4016,c_4001,c_3986,c_3763,c_3775,c_3299,c_3296,c_3293,c_3287,c_3284,c_3251,c_3212,c_37,c_35,c_34,c_33,c_32])).


%------------------------------------------------------------------------------
