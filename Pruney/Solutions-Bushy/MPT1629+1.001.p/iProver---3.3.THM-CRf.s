%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1629+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:01 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  179 (1120 expanded)
%              Number of clauses        :  112 ( 208 expanded)
%              Number of leaves         :   16 ( 350 expanded)
%              Depth                    :   25
%              Number of atoms          :  922 (7979 expanded)
%              Number of equality atoms :  143 ( 166 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f30,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f30,f29])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
              <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <~> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
            | ~ r1_waybel_0(X0,X1,X2) )
          & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
            | r1_waybel_0(X0,X1,X2) ) )
     => ( ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),sK7))
          | ~ r1_waybel_0(X0,X1,sK7) )
        & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),sK7))
          | r1_waybel_0(X0,X1,sK7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | r1_waybel_0(X0,X1,X2) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( r2_waybel_0(X0,sK6,k6_subset_1(u1_struct_0(X0),X2))
              | ~ r1_waybel_0(X0,sK6,X2) )
            & ( ~ r2_waybel_0(X0,sK6,k6_subset_1(u1_struct_0(X0),X2))
              | r1_waybel_0(X0,sK6,X2) ) )
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                  | ~ r1_waybel_0(X0,X1,X2) )
                & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                  | r1_waybel_0(X0,X1,X2) ) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_0(sK5,X1,k6_subset_1(u1_struct_0(sK5),X2))
                | ~ r1_waybel_0(sK5,X1,X2) )
              & ( ~ r2_waybel_0(sK5,X1,k6_subset_1(u1_struct_0(sK5),X2))
                | r1_waybel_0(sK5,X1,X2) ) )
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
      | ~ r1_waybel_0(sK5,sK6,sK7) )
    & ( ~ r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
      | r1_waybel_0(sK5,sK6,sK7) )
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f40,f39,f38])).

fof(f65,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
                      & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( ~ r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
    | ~ r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

cnf(c_6,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_611,plain,
    ( r2_waybel_0(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_612,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_616,plain,
    ( m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6))
    | r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_24,c_23,c_22])).

cnf(c_617,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_616])).

cnf(c_2577,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_671,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_672,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_676,plain,
    ( m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_24,c_23,c_22])).

cnf(c_677,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_2574,plain,
    ( r1_waybel_0(sK5,sK6,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK0(sK5,sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k2_waybel_0(X1,X0,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k2_waybel_0(X2,X1,X0),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK6 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k2_waybel_0(sK5,sK6,X0),u1_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( m1_subset_1(k2_waybel_0(sK5,sK6,X0),u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_24,c_23,c_22])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | m1_subset_1(k2_waybel_0(sK5,sK6,X0),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_739])).

cnf(c_2571,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k2_waybel_0(sK5,sK6,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_819,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_820,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_35,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_822,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_24,c_23,c_35])).

cnf(c_832,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK5) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_822])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_2569,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_2804,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2571,c_2569])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2585,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k6_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( r1_orders_2(X0,X1,sK0(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,X3)
    | ~ l1_waybel_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_struct_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_713,plain,
    ( r1_orders_2(X0,X1,sK0(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | sK6 != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_714,plain,
    ( r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0))
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X1)
    | r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_24,c_23,c_22])).

cnf(c_719,plain,
    ( r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0))
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_2572,plain,
    ( r1_orders_2(sK6,X0,sK0(sK5,sK6,X1,X0)) = iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_5,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,X3),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_629,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,X3),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_630,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_24,c_23,c_22])).

cnf(c_635,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK2(sK5,sK6,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_2576,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | r1_orders_2(sK6,sK2(sK5,sK6,X0),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_3259,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_2576])).

cnf(c_887,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X3,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,X2),X0)
    | sK0(sK5,sK6,X1,X3) != X2
    | sK2(sK5,sK6,X0) != X3
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_635,c_719])).

cnf(c_888,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) ),
    inference(unflattening,[status(thm)],[c_887])).

cnf(c_892,plain,
    ( ~ m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X1)
    | r2_waybel_0(sK5,sK6,X0)
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_24,c_23,c_22,c_612])).

cnf(c_893,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) ),
    inference(renaming,[status(thm)],[c_892])).

cnf(c_894,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_893])).

cnf(c_3985,plain,
    ( m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | r2_waybel_0(sK5,sK6,X0) = iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3259,c_894])).

cnf(c_3986,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,X0)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,X0))),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3985])).

cnf(c_3989,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(X0,X1)) = iProver_top
    | r1_waybel_0(sK5,sK6,X2) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X2,sK2(sK5,sK6,k6_subset_1(X0,X1))),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X2,sK2(sK5,sK6,k6_subset_1(X0,X1)))),X0) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X2,sK2(sK5,sK6,k6_subset_1(X0,X1)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_3986])).

cnf(c_12001,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)) = iProver_top
    | r1_waybel_0(sK5,sK6,X1) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X1,sK2(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0))),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X1,sK2(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_3989])).

cnf(c_0,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_692,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_693,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_697,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_24,c_23,c_22])).

cnf(c_698,plain,
    ( r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_697])).

cnf(c_2573,plain,
    ( r1_waybel_0(sK5,sK6,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK0(sK5,sK6,X0,X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_12016,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)) = iProver_top
    | r1_waybel_0(sK5,sK6,X0) = iProver_top
    | m1_subset_1(sK0(sK5,sK6,X0,sK2(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0))),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12001,c_2573])).

cnf(c_12148,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)) = iProver_top
    | r1_waybel_0(sK5,sK6,X0) = iProver_top
    | m1_subset_1(sK2(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_12016])).

cnf(c_12154,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),X0)) = iProver_top
    | r1_waybel_0(sK5,sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_12148])).

cnf(c_20,negated_conjecture,
    ( ~ r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
    | r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2581,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7)) != iProver_top
    | r1_waybel_0(sK5,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12201,plain,
    ( r1_waybel_0(sK5,sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12154,c_2581])).

cnf(c_19,negated_conjecture,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7))
    | ~ r1_waybel_0(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2582,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(u1_struct_0(sK5),sK7)) = iProver_top
    | r1_waybel_0(sK5,sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_653,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_654,plain,
    ( ~ r1_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_658,plain,
    ( m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6))
    | ~ r1_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_24,c_23,c_22])).

cnf(c_659,plain,
    ( ~ r1_waybel_0(sK5,sK6,X0)
    | m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_2575,plain,
    ( r1_waybel_0(sK5,sK6,X0) != iProver_top
    | m1_subset_1(sK1(sK5,sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_8,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_569,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_570,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_570,c_24,c_23,c_22])).

cnf(c_575,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_574])).

cnf(c_2579,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | r1_orders_2(sK6,X1,sK3(sK5,sK6,X0,X1)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_752,plain,
    ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_753,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1)
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_757,plain,
    ( r2_hidden(k2_waybel_0(sK5,sK6,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_753,c_24,c_23,c_22])).

cnf(c_758,plain,
    ( ~ r1_orders_2(sK6,sK1(sK5,sK6,X0),X1)
    | ~ r1_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) ),
    inference(renaming,[status(thm)],[c_757])).

cnf(c_2570,plain,
    ( r1_orders_2(sK6,sK1(sK5,sK6,X0),X1) != iProver_top
    | r1_waybel_0(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_3179,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) != iProver_top
    | m1_subset_1(sK3(sK5,sK6,X0,sK1(sK5,sK6,X1)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK1(sK5,sK6,X1),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,sK1(sK5,sK6,X1))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_2570])).

cnf(c_865,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X3,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,X2),X1)
    | sK3(sK5,sK6,X0,X3) != X2
    | sK1(sK5,sK6,X1) != X3
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_758])).

cnf(c_866,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ r1_waybel_0(sK5,sK6,X1)
    | ~ m1_subset_1(sK3(sK5,sK6,X0,sK1(sK5,sK6,X1)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK1(sK5,sK6,X1),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,sK1(sK5,sK6,X1))),X1) ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_9,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_548,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_549,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_553,plain,
    ( m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_24,c_23,c_22])).

cnf(c_554,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK5,sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_880,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ r1_waybel_0(sK5,sK6,X1)
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,sK1(sK5,sK6,X1))),X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_866,c_659,c_554])).

cnf(c_884,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,sK1(sK5,sK6,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_3723,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,sK1(sK5,sK6,X1))),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3179,c_884])).

cnf(c_7,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_590,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_591,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_waybel_0(sK5,sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_24,c_23,c_22])).

cnf(c_596,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_2578,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2584,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3171,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(X0,X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK3(sK5,sK6,k6_subset_1(X0,X1),X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_2584])).

cnf(c_3729,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(X0,X1)) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) != iProver_top
    | m1_subset_1(sK1(sK5,sK6,X1),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3723,c_3171])).

cnf(c_4164,plain,
    ( r2_waybel_0(sK5,sK6,k6_subset_1(X0,X1)) != iProver_top
    | r1_waybel_0(sK5,sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2575,c_3729])).

cnf(c_4169,plain,
    ( r1_waybel_0(sK5,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_4164])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12201,c_4169])).


%------------------------------------------------------------------------------
