%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:38 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 639 expanded)
%              Number of clauses        :   92 ( 230 expanded)
%              Number of leaves         :   23 ( 127 expanded)
%              Depth                    :   25
%              Number of atoms          :  909 (3630 expanded)
%              Number of equality atoms :  108 ( 316 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).

fof(f66,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,u1_struct_0(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,u1_struct_0(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0),u1_waybel_0(X0,sK6)))
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK5,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),u1_waybel_0(sK5,X1)))
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6)))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f54,f53])).

fof(f84,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
     => ( v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0))
        & l1_waybel_0(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0))
        & l1_waybel_0(sK4(X0),X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f51])).

fof(f74,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ~ r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6))) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0_61,X0_58)
    | ~ v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_10,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_304,plain,
    ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | r2_hidden(k2_waybel_0(X0_57,X1_57,sK3(X0_57,X1_57,X0_58,X0_59)),X0_58)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4511,plain,
    ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_xboole_0(X0_58) ),
    inference(resolution,[status(thm)],[c_314,c_304])).

cnf(c_24,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(o_2_4_waybel_9(X1,X0),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_290,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | m1_subset_1(o_2_4_waybel_9(X1_57,X0_57),u1_struct_0(X0_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4545,plain,
    ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ l1_waybel_0(X1_57,X2_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_xboole_0(X0_58) ),
    inference(resolution,[status(thm)],[c_4511,c_290])).

cnf(c_22,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_292,plain,
    ( r2_waybel_0(X0_57,X1_57,X0_58)
    | ~ r1_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4675,plain,
    ( ~ r1_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ l1_waybel_0(X1_57,X2_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_xboole_0(X0_58) ),
    inference(resolution,[status(thm)],[c_4545,c_292])).

cnf(c_23,plain,
    ( r1_waybel_0(X0,X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_291,plain,
    ( r1_waybel_0(X0_57,X1_57,u1_struct_0(X0_57))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_4993,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ l1_waybel_0(X0_57,X2_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X2_57)
    | ~ v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(resolution,[status(thm)],[c_4675,c_291])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_288,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_5019,plain,
    ( ~ l1_waybel_0(sK6,X0_57)
    | ~ v4_orders_2(sK6)
    | ~ v7_waybel_0(sK6)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK5)
    | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(resolution,[status(thm)],[c_4993,c_288])).

cnf(c_21,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_293,plain,
    ( l1_waybel_0(sK4(X0_57),X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_785,plain,
    ( l1_waybel_0(sK4(X0_57),X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_787,plain,
    ( r1_waybel_0(X0_57,X1_57,u1_struct_0(X0_57)) = iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_786,plain,
    ( r2_waybel_0(X0_57,X1_57,X0_58) = iProver_top
    | r1_waybel_0(X0_57,X1_57,X0_58) != iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_2789,plain,
    ( r2_waybel_0(X0_57,X1_57,u1_struct_0(X0_57)) = iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_786])).

cnf(c_788,plain,
    ( l1_waybel_0(X0_57,X1_57) != iProver_top
    | m1_subset_1(o_2_4_waybel_9(X1_57,X0_57),u1_struct_0(X0_57)) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_774,plain,
    ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(X1_57)) != iProver_top
    | r2_hidden(k2_waybel_0(X0_57,X1_57,sK3(X0_57,X1_57,X0_58,X0_59)),X0_58) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_764,plain,
    ( r2_hidden(X0_61,X0_58) != iProver_top
    | v1_xboole_0(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_2875,plain,
    ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(X1_57)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_764])).

cnf(c_3381,plain,
    ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
    | l1_waybel_0(X1_57,X2_57) != iProver_top
    | l1_waybel_0(X1_57,X0_57) != iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_2875])).

cnf(c_3457,plain,
    ( l1_waybel_0(X0_57,X1_57) != iProver_top
    | l1_waybel_0(X0_57,X2_57) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2789,c_3381])).

cnf(c_3894,plain,
    ( l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
    | v4_orders_2(sK4(X0_57)) != iProver_top
    | v7_waybel_0(sK4(X0_57)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK4(X0_57)) = iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_3457])).

cnf(c_18,plain,
    ( v7_waybel_0(sK4(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_296,plain,
    ( v7_waybel_0(sK4(X0_57))
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_366,plain,
    ( v7_waybel_0(sK4(X0_57)) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_19,plain,
    ( v4_orders_2(sK4(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_295,plain,
    ( v4_orders_2(sK4(X0_57))
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_367,plain,
    ( v4_orders_2(sK4(X0_57)) = iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_20,plain,
    ( ~ v2_struct_0(sK4(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_294,plain,
    ( ~ v2_struct_0(sK4(X0_57))
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_368,plain,
    ( v2_struct_0(sK4(X0_57)) != iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_4188,plain,
    ( v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3894,c_366,c_367,c_368])).

cnf(c_4189,plain,
    ( l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4188])).

cnf(c_4198,plain,
    ( v2_struct_0(X0_57) = iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_4189])).

cnf(c_4199,plain,
    ( v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4198])).

cnf(c_5024,plain,
    ( ~ l1_struct_0(X0_57)
    | v2_struct_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5019,c_4199])).

cnf(c_5025,plain,
    ( v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(renaming,[status(thm)],[c_5024])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_301,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X1_57)
    | k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59) = k2_waybel_0(X1_57,X0_57,X0_59) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_317,plain,
    ( X0_61 != X1_61
    | X2_61 != X1_61
    | X2_61 = X0_61 ),
    theory(equality)).

cnf(c_316,plain,
    ( X0_61 = X0_61 ),
    theory(equality)).

cnf(c_1417,plain,
    ( X0_61 != X1_61
    | X1_61 = X0_61 ),
    inference(resolution,[status(thm)],[c_317,c_316])).

cnf(c_2179,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X1_57)
    | k2_waybel_0(X1_57,X0_57,X0_59) = k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59) ),
    inference(resolution,[status(thm)],[c_301,c_1417])).

cnf(c_318,plain,
    ( ~ r2_hidden(X0_61,X0_58)
    | r2_hidden(X1_61,X0_58)
    | X1_61 != X0_61 ),
    theory(equality)).

cnf(c_2376,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59),X0_58)
    | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),X0_58)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X1_57) ),
    inference(resolution,[status(thm)],[c_2179,c_318])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_313,plain,
    ( ~ v1_funct_2(X0_59,X0_58,X1_58)
    | ~ m1_subset_1(X1_59,X0_58)
    | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
    | r2_hidden(k3_funct_2(X0_58,X1_58,X0_59,X1_59),k2_relset_1(X0_58,X1_58,X0_59))
    | ~ v1_funct_1(X0_59)
    | v1_xboole_0(X1_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2490,plain,
    ( ~ v1_funct_2(u1_waybel_0(X0_57,X1_57),u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | ~ m1_subset_1(u1_waybel_0(X0_57,X1_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | r2_hidden(k2_waybel_0(X0_57,X1_57,X0_59),k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(u1_waybel_0(X0_57,X1_57))
    | v1_xboole_0(u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(resolution,[status(thm)],[c_2376,c_313])).

cnf(c_16,plain,
    ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_298,plain,
    ( v1_funct_2(u1_waybel_0(X0_57,X1_57),u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3938,plain,
    ( ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | ~ m1_subset_1(u1_waybel_0(X0_57,X1_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | r2_hidden(k2_waybel_0(X0_57,X1_57,X0_59),k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(u1_waybel_0(X0_57,X1_57))
    | v1_xboole_0(u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2490,c_298])).

cnf(c_3939,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | ~ m1_subset_1(u1_waybel_0(X1_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | ~ l1_struct_0(X1_57)
    | ~ v1_funct_1(u1_waybel_0(X1_57,X0_57))
    | v1_xboole_0(u1_struct_0(X1_57))
    | v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(renaming,[status(thm)],[c_3938])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_299,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | m1_subset_1(u1_waybel_0(X1_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_17,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_297,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ l1_struct_0(X1_57)
    | v1_funct_1(u1_waybel_0(X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3944,plain,
    ( ~ l1_struct_0(X1_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
    | ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57))
    | v1_xboole_0(u1_struct_0(X0_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_299,c_297])).

cnf(c_3945,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
    | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X1_57)
    | v1_xboole_0(u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(renaming,[status(thm)],[c_3944])).

cnf(c_3,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_311,plain,
    ( r1_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | ~ r2_hidden(k2_waybel_0(X0_57,X1_57,sK0(X0_57,X1_57,X0_58,X0_59)),X0_58)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3986,plain,
    ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | ~ m1_subset_1(sK0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)),X0_59),u1_struct_0(X1_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | v1_xboole_0(u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(resolution,[status(thm)],[c_3945,c_311])).

cnf(c_5,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_309,plain,
    ( r1_waybel_0(X0_57,X1_57,X0_58)
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | m1_subset_1(sK0(X0_57,X1_57,X0_58,X0_59),u1_struct_0(X1_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4004,plain,
    ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | v1_xboole_0(u1_struct_0(X0_57))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3986,c_309])).

cnf(c_4201,plain,
    ( ~ l1_struct_0(X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | ~ l1_waybel_0(X1_57,X0_57)
    | r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4004,c_4199])).

cnf(c_4202,plain,
    ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_struct_0(X0_57)
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(renaming,[status(thm)],[c_4201])).

cnf(c_4237,plain,
    ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
    | ~ l1_waybel_0(X1_57,X0_57)
    | ~ l1_waybel_0(X1_57,X2_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X2_57)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(X2_57)
    | v1_xboole_0(u1_struct_0(X1_57)) ),
    inference(resolution,[status(thm)],[c_4202,c_290])).

cnf(c_4277,plain,
    ( r1_waybel_0(X0_57,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0_57),u1_waybel_0(X0_57,sK6)))
    | ~ l1_waybel_0(sK6,X0_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_4237,c_288])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_25,negated_conjecture,
    ( ~ r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4279,plain,
    ( r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6)))
    | ~ l1_waybel_0(sK6,sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_4277])).

cnf(c_4387,plain,
    ( v1_xboole_0(u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4277,c_29,c_28,c_27,c_26,c_25,c_4279])).

cnf(c_5106,plain,
    ( v2_struct_0(sK6)
    | ~ l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_5025,c_4387])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_312,plain,
    ( ~ l1_orders_2(X0_57)
    | l1_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_14,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_300,plain,
    ( ~ l1_waybel_0(X0_57,X1_57)
    | l1_orders_2(X0_57)
    | ~ l1_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1245,plain,
    ( l1_orders_2(sK6)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_300,c_288])).

cnf(c_1149,plain,
    ( ~ l1_waybel_0(sK6,sK5)
    | l1_orders_2(sK6)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_1252,plain,
    ( l1_orders_2(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_28,c_26,c_1149])).

cnf(c_1320,plain,
    ( l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_312,c_1252])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5106,c_1320,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.16/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.02  
% 3.16/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.02  
% 3.16/1.02  ------  iProver source info
% 3.16/1.02  
% 3.16/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.02  git: non_committed_changes: false
% 3.16/1.02  git: last_make_outside_of_git: false
% 3.16/1.02  
% 3.16/1.02  ------ 
% 3.16/1.02  ------ Parsing...
% 3.16/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.02  
% 3.16/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.16/1.02  
% 3.16/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.02  
% 3.16/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.02  ------ Proving...
% 3.16/1.02  ------ Problem Properties 
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  clauses                                 30
% 3.16/1.02  conjectures                             5
% 3.16/1.02  EPR                                     8
% 3.16/1.02  Horn                                    15
% 3.16/1.02  unary                                   5
% 3.16/1.02  binary                                  6
% 3.16/1.02  lits                                    132
% 3.16/1.02  lits eq                                 1
% 3.16/1.02  fd_pure                                 0
% 3.16/1.02  fd_pseudo                               0
% 3.16/1.02  fd_cond                                 0
% 3.16/1.02  fd_pseudo_cond                          0
% 3.16/1.02  AC symbols                              0
% 3.16/1.02  
% 3.16/1.02  ------ Input Options Time Limit: Unbounded
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  ------ 
% 3.16/1.02  Current options:
% 3.16/1.02  ------ 
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  ------ Proving...
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  % SZS status Theorem for theBenchmark.p
% 3.16/1.02  
% 3.16/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.02  
% 3.16/1.02  fof(f1,axiom,(
% 3.16/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f15,plain,(
% 3.16/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.16/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 3.16/1.02  
% 3.16/1.02  fof(f19,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.16/1.02    inference(ennf_transformation,[],[f15])).
% 3.16/1.02  
% 3.16/1.02  fof(f56,plain,(
% 3.16/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f19])).
% 3.16/1.02  
% 3.16/1.02  fof(f5,axiom,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f25,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f5])).
% 3.16/1.02  
% 3.16/1.02  fof(f26,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f25])).
% 3.16/1.02  
% 3.16/1.02  fof(f46,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(nnf_transformation,[],[f26])).
% 3.16/1.02  
% 3.16/1.02  fof(f47,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(rectify,[],[f46])).
% 3.16/1.02  
% 3.16/1.02  fof(f49,plain,(
% 3.16/1.02    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f48,plain,(
% 3.16/1.02    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f50,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).
% 3.16/1.02  
% 3.16/1.02  fof(f66,plain,(
% 3.16/1.02    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f50])).
% 3.16/1.02  
% 3.16/1.02  fof(f12,axiom,(
% 3.16/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f37,plain,(
% 3.16/1.02    ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f12])).
% 3.16/1.02  
% 3.16/1.02  fof(f38,plain,(
% 3.16/1.02    ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f37])).
% 3.16/1.02  
% 3.16/1.02  fof(f80,plain,(
% 3.16/1.02    ( ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f38])).
% 3.16/1.02  
% 3.16/1.02  fof(f10,axiom,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f33,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f10])).
% 3.16/1.02  
% 3.16/1.02  fof(f34,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f33])).
% 3.16/1.02  
% 3.16/1.02  fof(f78,plain,(
% 3.16/1.02    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f34])).
% 3.16/1.02  
% 3.16/1.02  fof(f11,axiom,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f35,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f11])).
% 3.16/1.02  
% 3.16/1.02  fof(f36,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f35])).
% 3.16/1.02  
% 3.16/1.02  fof(f79,plain,(
% 3.16/1.02    ( ! [X0,X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f36])).
% 3.16/1.02  
% 3.16/1.02  fof(f13,conjecture,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f14,negated_conjecture,(
% 3.16/1.02    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 3.16/1.02    inference(negated_conjecture,[],[f13])).
% 3.16/1.02  
% 3.16/1.02  fof(f39,plain,(
% 3.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f14])).
% 3.16/1.02  
% 3.16/1.02  fof(f40,plain,(
% 3.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f39])).
% 3.16/1.02  
% 3.16/1.02  fof(f54,plain,(
% 3.16/1.02    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0),u1_waybel_0(X0,sK6))) & l1_waybel_0(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f53,plain,(
% 3.16/1.02    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK5,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK5),u1_waybel_0(sK5,X1))) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f55,plain,(
% 3.16/1.02    (~r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6))) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 3.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f40,f54,f53])).
% 3.16/1.02  
% 3.16/1.02  fof(f84,plain,(
% 3.16/1.02    l1_waybel_0(sK6,sK5)),
% 3.16/1.02    inference(cnf_transformation,[],[f55])).
% 3.16/1.02  
% 3.16/1.02  fof(f9,axiom,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f16,plain,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 3.16/1.02    inference(pure_predicate_removal,[],[f9])).
% 3.16/1.02  
% 3.16/1.02  fof(f17,plain,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 3.16/1.02    inference(pure_predicate_removal,[],[f16])).
% 3.16/1.02  
% 3.16/1.02  fof(f18,plain,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 3.16/1.02    inference(pure_predicate_removal,[],[f17])).
% 3.16/1.02  
% 3.16/1.02  fof(f32,plain,(
% 3.16/1.02    ! [X0] : (? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.16/1.02    inference(ennf_transformation,[],[f18])).
% 3.16/1.02  
% 3.16/1.02  fof(f51,plain,(
% 3.16/1.02    ! [X0] : (? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)) => (v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)) & l1_waybel_0(sK4(X0),X0)))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f52,plain,(
% 3.16/1.02    ! [X0] : ((v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)) & l1_waybel_0(sK4(X0),X0)) | ~l1_struct_0(X0))),
% 3.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f51])).
% 3.16/1.02  
% 3.16/1.02  fof(f74,plain,(
% 3.16/1.02    ( ! [X0] : (l1_waybel_0(sK4(X0),X0) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f52])).
% 3.16/1.02  
% 3.16/1.02  fof(f77,plain,(
% 3.16/1.02    ( ! [X0] : (v7_waybel_0(sK4(X0)) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f52])).
% 3.16/1.02  
% 3.16/1.02  fof(f76,plain,(
% 3.16/1.02    ( ! [X0] : (v4_orders_2(sK4(X0)) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f52])).
% 3.16/1.02  
% 3.16/1.02  fof(f75,plain,(
% 3.16/1.02    ( ! [X0] : (~v2_struct_0(sK4(X0)) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f52])).
% 3.16/1.02  
% 3.16/1.02  fof(f6,axiom,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f27,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f6])).
% 3.16/1.02  
% 3.16/1.02  fof(f28,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f27])).
% 3.16/1.02  
% 3.16/1.02  fof(f69,plain,(
% 3.16/1.02    ( ! [X2,X0,X1] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f28])).
% 3.16/1.02  
% 3.16/1.02  fof(f2,axiom,(
% 3.16/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f20,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.16/1.02    inference(ennf_transformation,[],[f2])).
% 3.16/1.02  
% 3.16/1.02  fof(f21,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.16/1.02    inference(flattening,[],[f20])).
% 3.16/1.02  
% 3.16/1.02  fof(f57,plain,(
% 3.16/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f21])).
% 3.16/1.02  
% 3.16/1.02  fof(f8,axiom,(
% 3.16/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f30,plain,(
% 3.16/1.02    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f8])).
% 3.16/1.02  
% 3.16/1.02  fof(f31,plain,(
% 3.16/1.02    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f30])).
% 3.16/1.02  
% 3.16/1.02  fof(f72,plain,(
% 3.16/1.02    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f31])).
% 3.16/1.02  
% 3.16/1.02  fof(f73,plain,(
% 3.16/1.02    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f31])).
% 3.16/1.02  
% 3.16/1.02  fof(f71,plain,(
% 3.16/1.02    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f31])).
% 3.16/1.02  
% 3.16/1.02  fof(f4,axiom,(
% 3.16/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f23,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.02    inference(ennf_transformation,[],[f4])).
% 3.16/1.02  
% 3.16/1.02  fof(f24,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(flattening,[],[f23])).
% 3.16/1.02  
% 3.16/1.02  fof(f41,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(nnf_transformation,[],[f24])).
% 3.16/1.02  
% 3.16/1.02  fof(f42,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(rectify,[],[f41])).
% 3.16/1.02  
% 3.16/1.02  fof(f44,plain,(
% 3.16/1.02    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f43,plain,(
% 3.16/1.02    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))))),
% 3.16/1.02    introduced(choice_axiom,[])).
% 3.16/1.02  
% 3.16/1.02  fof(f45,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 3.16/1.02  
% 3.16/1.02  fof(f63,plain,(
% 3.16/1.02    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f45])).
% 3.16/1.02  
% 3.16/1.02  fof(f61,plain,(
% 3.16/1.02    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f45])).
% 3.16/1.02  
% 3.16/1.02  fof(f81,plain,(
% 3.16/1.02    ~v2_struct_0(sK5)),
% 3.16/1.02    inference(cnf_transformation,[],[f55])).
% 3.16/1.02  
% 3.16/1.02  fof(f82,plain,(
% 3.16/1.02    l1_struct_0(sK5)),
% 3.16/1.02    inference(cnf_transformation,[],[f55])).
% 3.16/1.02  
% 3.16/1.02  fof(f83,plain,(
% 3.16/1.02    ~v2_struct_0(sK6)),
% 3.16/1.02    inference(cnf_transformation,[],[f55])).
% 3.16/1.02  
% 3.16/1.02  fof(f85,plain,(
% 3.16/1.02    ~r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6)))),
% 3.16/1.02    inference(cnf_transformation,[],[f55])).
% 3.16/1.02  
% 3.16/1.02  fof(f3,axiom,(
% 3.16/1.02    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f22,plain,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.16/1.02    inference(ennf_transformation,[],[f3])).
% 3.16/1.02  
% 3.16/1.02  fof(f58,plain,(
% 3.16/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f22])).
% 3.16/1.02  
% 3.16/1.02  fof(f7,axiom,(
% 3.16/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 3.16/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.02  
% 3.16/1.02  fof(f29,plain,(
% 3.16/1.02    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 3.16/1.02    inference(ennf_transformation,[],[f7])).
% 3.16/1.02  
% 3.16/1.02  fof(f70,plain,(
% 3.16/1.02    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 3.16/1.02    inference(cnf_transformation,[],[f29])).
% 3.16/1.02  
% 3.16/1.02  cnf(c_0,plain,
% 3.16/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.16/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_314,plain,
% 3.16/1.02      ( ~ r2_hidden(X0_61,X0_58) | ~ v1_xboole_0(X0_58) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_10,plain,
% 3.16/1.02      ( ~ r2_waybel_0(X0,X1,X2)
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_304,plain,
% 3.16/1.02      ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X0_57,X1_57,sK3(X0_57,X1_57,X0_58,X0_59)),X0_58)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4511,plain,
% 3.16/1.02      ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ v1_xboole_0(X0_58) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_314,c_304]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_24,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 3.16/1.02      | m1_subset_1(o_2_4_waybel_9(X1,X0),u1_struct_0(X0))
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | ~ l1_struct_0(X1) ),
% 3.16/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_290,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | m1_subset_1(o_2_4_waybel_9(X1_57,X0_57),u1_struct_0(X0_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_24]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4545,plain,
% 3.16/1.02      ( ~ r2_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X2_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X2_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X2_57)
% 3.16/1.02      | ~ v1_xboole_0(X0_58) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4511,c_290]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_22,plain,
% 3.16/1.02      ( r2_waybel_0(X0,X1,X2)
% 3.16/1.02      | ~ r1_waybel_0(X0,X1,X2)
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ v4_orders_2(X1)
% 3.16/1.02      | ~ v7_waybel_0(X1)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_292,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ r1_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ v4_orders_2(X1_57)
% 3.16/1.02      | ~ v7_waybel_0(X1_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4675,plain,
% 3.16/1.02      ( ~ r1_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X2_57)
% 3.16/1.02      | ~ v4_orders_2(X1_57)
% 3.16/1.02      | ~ v7_waybel_0(X1_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X2_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X2_57)
% 3.16/1.02      | ~ v1_xboole_0(X0_58) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4545,c_292]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_23,plain,
% 3.16/1.02      ( r1_waybel_0(X0,X1,u1_struct_0(X0))
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ v4_orders_2(X1)
% 3.16/1.02      | ~ v7_waybel_0(X1)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_291,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,u1_struct_0(X0_57))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ v4_orders_2(X1_57)
% 3.16/1.02      | ~ v7_waybel_0(X1_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4993,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ l1_waybel_0(X0_57,X2_57)
% 3.16/1.02      | ~ v4_orders_2(X0_57)
% 3.16/1.02      | ~ v7_waybel_0(X0_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X2_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | ~ l1_struct_0(X2_57)
% 3.16/1.02      | ~ v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4675,c_291]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_26,negated_conjecture,
% 3.16/1.02      ( l1_waybel_0(sK6,sK5) ),
% 3.16/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_288,negated_conjecture,
% 3.16/1.02      ( l1_waybel_0(sK6,sK5) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_26]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_5019,plain,
% 3.16/1.02      ( ~ l1_waybel_0(sK6,X0_57)
% 3.16/1.02      | ~ v4_orders_2(sK6)
% 3.16/1.02      | ~ v7_waybel_0(sK6)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(sK6)
% 3.16/1.02      | v2_struct_0(sK5)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(sK5)
% 3.16/1.02      | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4993,c_288]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_21,plain,
% 3.16/1.02      ( l1_waybel_0(sK4(X0),X0) | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_293,plain,
% 3.16/1.02      ( l1_waybel_0(sK4(X0_57),X0_57) | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_21]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_785,plain,
% 3.16/1.02      ( l1_waybel_0(sK4(X0_57),X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_787,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,u1_struct_0(X0_57)) = iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | v4_orders_2(X1_57) != iProver_top
% 3.16/1.02      | v7_waybel_0(X1_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_786,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,X0_58) = iProver_top
% 3.16/1.02      | r1_waybel_0(X0_57,X1_57,X0_58) != iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | v4_orders_2(X1_57) != iProver_top
% 3.16/1.02      | v7_waybel_0(X1_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2789,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,u1_struct_0(X0_57)) = iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | v4_orders_2(X1_57) != iProver_top
% 3.16/1.02      | v7_waybel_0(X1_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_787,c_786]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_788,plain,
% 3.16/1.02      ( l1_waybel_0(X0_57,X1_57) != iProver_top
% 3.16/1.02      | m1_subset_1(o_2_4_waybel_9(X1_57,X0_57),u1_struct_0(X0_57)) = iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X1_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_774,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | m1_subset_1(X0_59,u1_struct_0(X1_57)) != iProver_top
% 3.16/1.02      | r2_hidden(k2_waybel_0(X0_57,X1_57,sK3(X0_57,X1_57,X0_58,X0_59)),X0_58) = iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_764,plain,
% 3.16/1.02      ( r2_hidden(X0_61,X0_58) != iProver_top
% 3.16/1.02      | v1_xboole_0(X0_58) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2875,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | m1_subset_1(X0_59,u1_struct_0(X1_57)) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(X0_58) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_774,c_764]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3381,plain,
% 3.16/1.02      ( r2_waybel_0(X0_57,X1_57,X0_58) != iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X2_57) != iProver_top
% 3.16/1.02      | l1_waybel_0(X1_57,X0_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X2_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X2_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(X0_58) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_788,c_2875]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3457,plain,
% 3.16/1.02      ( l1_waybel_0(X0_57,X1_57) != iProver_top
% 3.16/1.02      | l1_waybel_0(X0_57,X2_57) != iProver_top
% 3.16/1.02      | v4_orders_2(X0_57) != iProver_top
% 3.16/1.02      | v7_waybel_0(X0_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X2_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X1_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X2_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_2789,c_3381]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3894,plain,
% 3.16/1.02      ( l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
% 3.16/1.02      | v4_orders_2(sK4(X0_57)) != iProver_top
% 3.16/1.02      | v7_waybel_0(sK4(X0_57)) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | v2_struct_0(sK4(X0_57)) = iProver_top
% 3.16/1.02      | l1_struct_0(X1_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_785,c_3457]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_18,plain,
% 3.16/1.02      ( v7_waybel_0(sK4(X0)) | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_296,plain,
% 3.16/1.02      ( v7_waybel_0(sK4(X0_57)) | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_366,plain,
% 3.16/1.02      ( v7_waybel_0(sK4(X0_57)) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_19,plain,
% 3.16/1.02      ( v4_orders_2(sK4(X0)) | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_295,plain,
% 3.16/1.02      ( v4_orders_2(sK4(X0_57)) | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_367,plain,
% 3.16/1.02      ( v4_orders_2(sK4(X0_57)) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_20,plain,
% 3.16/1.02      ( ~ v2_struct_0(sK4(X0)) | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_294,plain,
% 3.16/1.02      ( ~ v2_struct_0(sK4(X0_57)) | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_20]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_368,plain,
% 3.16/1.02      ( v2_struct_0(sK4(X0_57)) != iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top ),
% 3.16/1.02      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4188,plain,
% 3.16/1.02      ( v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X1_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_3894,c_366,c_367,c_368]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4189,plain,
% 3.16/1.02      ( l1_waybel_0(sK4(X0_57),X1_57) != iProver_top
% 3.16/1.02      | v2_struct_0(X1_57) = iProver_top
% 3.16/1.02      | v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X1_57) != iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
% 3.16/1.02      inference(renaming,[status(thm)],[c_4188]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4198,plain,
% 3.16/1.02      ( v2_struct_0(X0_57) = iProver_top
% 3.16/1.02      | l1_struct_0(X0_57) != iProver_top
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
% 3.16/1.02      inference(superposition,[status(thm)],[c_785,c_4189]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4199,plain,
% 3.16/1.02      ( v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4198]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_5024,plain,
% 3.16/1.02      ( ~ l1_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_5019,c_4199]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_5025,plain,
% 3.16/1.02      ( v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(renaming,[status(thm)],[c_5024]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_13,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 3.16/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | ~ l1_struct_0(X1)
% 3.16/1.02      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
% 3.16/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_301,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59) = k2_waybel_0(X1_57,X0_57,X0_59) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_317,plain,
% 3.16/1.02      ( X0_61 != X1_61 | X2_61 != X1_61 | X2_61 = X0_61 ),
% 3.16/1.02      theory(equality) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_316,plain,( X0_61 = X0_61 ),theory(equality) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1417,plain,
% 3.16/1.02      ( X0_61 != X1_61 | X1_61 = X0_61 ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_317,c_316]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2179,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | k2_waybel_0(X1_57,X0_57,X0_59) = k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_301,c_1417]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_318,plain,
% 3.16/1.02      ( ~ r2_hidden(X0_61,X0_58)
% 3.16/1.02      | r2_hidden(X1_61,X0_58)
% 3.16/1.02      | X1_61 != X0_61 ),
% 3.16/1.02      theory(equality) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2376,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | ~ r2_hidden(k3_funct_2(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57),X0_59),X0_58)
% 3.16/1.02      | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),X0_58)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_2179,c_318]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1,plain,
% 3.16/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.02      | ~ m1_subset_1(X3,X1)
% 3.16/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.02      | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
% 3.16/1.02      | ~ v1_funct_1(X0)
% 3.16/1.02      | v1_xboole_0(X1)
% 3.16/1.02      | v1_xboole_0(X2) ),
% 3.16/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_313,plain,
% 3.16/1.02      ( ~ v1_funct_2(X0_59,X0_58,X1_58)
% 3.16/1.02      | ~ m1_subset_1(X1_59,X0_58)
% 3.16/1.02      | ~ m1_subset_1(X0_59,k1_zfmisc_1(k2_zfmisc_1(X0_58,X1_58)))
% 3.16/1.02      | r2_hidden(k3_funct_2(X0_58,X1_58,X0_59,X1_59),k2_relset_1(X0_58,X1_58,X0_59))
% 3.16/1.02      | ~ v1_funct_1(X0_59)
% 3.16/1.02      | v1_xboole_0(X1_58)
% 3.16/1.02      | v1_xboole_0(X0_58) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2490,plain,
% 3.16/1.02      ( ~ v1_funct_2(u1_waybel_0(X0_57,X1_57),u1_struct_0(X1_57),u1_struct_0(X0_57))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | ~ m1_subset_1(u1_waybel_0(X0_57,X1_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X0_57,X1_57,X0_59),k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ v1_funct_1(u1_waybel_0(X0_57,X1_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_2376,c_313]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_16,plain,
% 3.16/1.02      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_298,plain,
% 3.16/1.02      ( v1_funct_2(u1_waybel_0(X0_57,X1_57),u1_struct_0(X1_57),u1_struct_0(X0_57))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3938,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | ~ m1_subset_1(u1_waybel_0(X0_57,X1_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X0_57,X1_57,X0_59),k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ v1_funct_1(u1_waybel_0(X0_57,X1_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_2490,c_298]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3939,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | ~ m1_subset_1(u1_waybel_0(X1_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | ~ v1_funct_1(u1_waybel_0(X1_57,X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(renaming,[status(thm)],[c_3938]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_15,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 3.16/1.02      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.16/1.02      | ~ l1_struct_0(X1) ),
% 3.16/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_299,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | m1_subset_1(u1_waybel_0(X1_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 3.16/1.02      | ~ l1_struct_0(X1_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_17,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0,X1)
% 3.16/1.02      | ~ l1_struct_0(X1)
% 3.16/1.02      | v1_funct_1(u1_waybel_0(X1,X0)) ),
% 3.16/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_297,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | v1_funct_1(u1_waybel_0(X1_57,X0_57)) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3944,plain,
% 3.16/1.02      ( ~ l1_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
% 3.16/1.02      | ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57)) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_3939,c_299,c_297]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3945,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X0_57))
% 3.16/1.02      | r2_hidden(k2_waybel_0(X1_57,X0_57,X0_59),k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),u1_waybel_0(X1_57,X0_57)))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(renaming,[status(thm)],[c_3944]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3,plain,
% 3.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.16/1.02      | ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_311,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | ~ r2_hidden(k2_waybel_0(X0_57,X1_57,sK0(X0_57,X1_57,X0_58,X0_59)),X0_58)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_3986,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | ~ m1_subset_1(sK0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)),X0_59),u1_struct_0(X1_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_3945,c_311]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_5,plain,
% 3.16/1.02      ( r1_waybel_0(X0,X1,X2)
% 3.16/1.02      | ~ l1_waybel_0(X1,X0)
% 3.16/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.16/1.02      | m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))
% 3.16/1.02      | v2_struct_0(X0)
% 3.16/1.02      | v2_struct_0(X1)
% 3.16/1.02      | ~ l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_309,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,X0_58)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | m1_subset_1(sK0(X0_57,X1_57,X0_58,X0_59),u1_struct_0(X1_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4004,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X0_57))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(forward_subsumption_resolution,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_3986,c_309]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4201,plain,
% 3.16/1.02      ( ~ l1_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_4004,c_4199]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4202,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ m1_subset_1(X0_59,u1_struct_0(X1_57))
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(renaming,[status(thm)],[c_4201]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4237,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,X1_57,k2_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),u1_waybel_0(X0_57,X1_57)))
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X0_57)
% 3.16/1.02      | ~ l1_waybel_0(X1_57,X2_57)
% 3.16/1.02      | v2_struct_0(X1_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(X2_57)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X2_57)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(X1_57)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4202,c_290]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4277,plain,
% 3.16/1.02      ( r1_waybel_0(X0_57,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(X0_57),u1_waybel_0(X0_57,sK6)))
% 3.16/1.02      | ~ l1_waybel_0(sK6,X0_57)
% 3.16/1.02      | v2_struct_0(X0_57)
% 3.16/1.02      | v2_struct_0(sK6)
% 3.16/1.02      | v2_struct_0(sK5)
% 3.16/1.02      | ~ l1_struct_0(X0_57)
% 3.16/1.02      | ~ l1_struct_0(sK5)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(sK6)) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_4237,c_288]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_29,negated_conjecture,
% 3.16/1.02      ( ~ v2_struct_0(sK5) ),
% 3.16/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_28,negated_conjecture,
% 3.16/1.02      ( l1_struct_0(sK5) ),
% 3.16/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_27,negated_conjecture,
% 3.16/1.02      ( ~ v2_struct_0(sK6) ),
% 3.16/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_25,negated_conjecture,
% 3.16/1.02      ( ~ r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6))) ),
% 3.16/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4279,plain,
% 3.16/1.02      ( r1_waybel_0(sK5,sK6,k2_relset_1(u1_struct_0(sK6),u1_struct_0(sK5),u1_waybel_0(sK5,sK6)))
% 3.16/1.02      | ~ l1_waybel_0(sK6,sK5)
% 3.16/1.02      | v2_struct_0(sK6)
% 3.16/1.02      | v2_struct_0(sK5)
% 3.16/1.02      | ~ l1_struct_0(sK5)
% 3.16/1.02      | v1_xboole_0(u1_struct_0(sK6)) ),
% 3.16/1.02      inference(instantiation,[status(thm)],[c_4277]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_4387,plain,
% 3.16/1.02      ( v1_xboole_0(u1_struct_0(sK6)) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_4277,c_29,c_28,c_27,c_26,c_25,c_4279]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_5106,plain,
% 3.16/1.02      ( v2_struct_0(sK6) | ~ l1_struct_0(sK6) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_5025,c_4387]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_2,plain,
% 3.16/1.02      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.16/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_312,plain,
% 3.16/1.02      ( ~ l1_orders_2(X0_57) | l1_struct_0(X0_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_14,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 3.16/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_300,plain,
% 3.16/1.02      ( ~ l1_waybel_0(X0_57,X1_57)
% 3.16/1.02      | l1_orders_2(X0_57)
% 3.16/1.02      | ~ l1_struct_0(X1_57) ),
% 3.16/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1245,plain,
% 3.16/1.02      ( l1_orders_2(sK6) | ~ l1_struct_0(sK5) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_300,c_288]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1149,plain,
% 3.16/1.02      ( ~ l1_waybel_0(sK6,sK5) | l1_orders_2(sK6) | ~ l1_struct_0(sK5) ),
% 3.16/1.02      inference(instantiation,[status(thm)],[c_300]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1252,plain,
% 3.16/1.02      ( l1_orders_2(sK6) ),
% 3.16/1.02      inference(global_propositional_subsumption,
% 3.16/1.02                [status(thm)],
% 3.16/1.02                [c_1245,c_28,c_26,c_1149]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(c_1320,plain,
% 3.16/1.02      ( l1_struct_0(sK6) ),
% 3.16/1.02      inference(resolution,[status(thm)],[c_312,c_1252]) ).
% 3.16/1.02  
% 3.16/1.02  cnf(contradiction,plain,
% 3.16/1.02      ( $false ),
% 3.16/1.02      inference(minisat,[status(thm)],[c_5106,c_1320,c_27]) ).
% 3.16/1.02  
% 3.16/1.02  
% 3.16/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.02  
% 3.16/1.02  ------                               Statistics
% 3.16/1.02  
% 3.16/1.02  ------ Selected
% 3.16/1.02  
% 3.16/1.02  total_time:                             0.249
% 3.16/1.02  
%------------------------------------------------------------------------------
