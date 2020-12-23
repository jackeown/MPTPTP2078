%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:18 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 755 expanded)
%              Number of clauses        :  107 ( 190 expanded)
%              Number of leaves         :   18 ( 206 expanded)
%              Depth                    :   25
%              Number of atoms          :  994 (5995 expanded)
%              Number of equality atoms :   80 ( 112 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f29])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v1_yellow_6(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
          & l1_waybel_0(X1,X0)
          & v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ~ r2_hidden(k4_yellow_6(X0,sK7),k10_yellow_6(X0,sK7))
        & l1_waybel_0(sK7,X0)
        & v1_yellow_6(sK7,X0)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))
            & l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k4_yellow_6(sK6,X1),k10_yellow_6(sK6,X1))
          & l1_waybel_0(X1,sK6)
          & v1_yellow_6(X1,sK6)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7))
    & l1_waybel_0(sK7,sK6)
    & v1_yellow_6(sK7,sK6)
    & v7_waybel_0(sK7)
    & v4_orders_2(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f44,f43])).

fof(f72,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
                      & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v1_yellow_6(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v1_yellow_6(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v1_yellow_6(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
        & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
        & m1_connsp_2(sK4(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK3(X0,X1,X2)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
                        & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
                            & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f66,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

cnf(c_0,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2850,plain,
    ( m1_subset_1(sK0(X0_56),X0_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3204,plain,
    ( m1_subset_1(sK0(X0_56),X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2850])).

cnf(c_20,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_401,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1258,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_25])).

cnf(c_1259,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1258])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1263,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK6)
    | r1_waybel_0(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_27])).

cnf(c_1264,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1263])).

cnf(c_1487,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK7 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1264])).

cnf(c_1488,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1487])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1492,plain,
    ( m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_24])).

cnf(c_1493,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1492])).

cnf(c_2834,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1493])).

cnf(c_3220,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2834])).

cnf(c_18,plain,
    ( ~ v1_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( v1_yellow_6(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_316,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
    | sK7 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_317,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | ~ l1_struct_0(sK6)
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_23,negated_conjecture,
    ( v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_89,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_27,c_25,c_24,c_23,c_22,c_20,c_89])).

cnf(c_2848,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_3206,plain,
    ( k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2848])).

cnf(c_3809,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3220,c_3206])).

cnf(c_4099,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | r1_waybel_0(sK6,sK7,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3204,c_3809])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_836,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_837,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_841,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_837,c_24,c_23])).

cnf(c_842,plain,
    ( ~ l1_waybel_0(sK7,X0)
    | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_841])).

cnf(c_13,plain,
    ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_689,plain,
    ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_690,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_694,plain,
    ( v2_struct_0(X0)
    | ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_24,c_23])).

cnf(c_695,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_694])).

cnf(c_861,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_842,c_695])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_996,plain,
    ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_861,c_26])).

cnf(c_997,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | ~ l1_waybel_0(sK7,sK6)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_996])).

cnf(c_1001,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_27,c_25,c_20])).

cnf(c_2846,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55))
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_3208,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55)) != iProver_top
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_4130,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,X0_55),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4099,c_3208])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2849,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3205,plain,
    ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_4222,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4130,c_3205])).

cnf(c_17,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_480,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_481,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1333,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_481,c_25])).

cnf(c_1334,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1333])).

cnf(c_1338,plain,
    ( m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
    | ~ l1_waybel_0(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1334,c_27])).

cnf(c_1339,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_1338])).

cnf(c_1462,plain,
    ( m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
    | sK7 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1339])).

cnf(c_1463,plain,
    ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1462])).

cnf(c_1464,plain,
    ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_4318,plain,
    ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4222,c_1464])).

cnf(c_4,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_427,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_1233,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_427,c_25])).

cnf(c_1234,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_1238,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ l1_waybel_0(X0,sK6)
    | r1_waybel_0(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_27])).

cnf(c_1239,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1238])).

cnf(c_1508,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK7 != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1239])).

cnf(c_1509,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_1508])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1509,c_24])).

cnf(c_1514,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_1513])).

cnf(c_2833,plain,
    ( r1_waybel_0(sK6,sK7,X0_55)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_1514])).

cnf(c_3221,plain,
    ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
    | r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55) != iProver_top
    | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2833])).

cnf(c_4321,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
    | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4318,c_3221])).

cnf(c_3,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_175,plain,
    ( r2_hidden(X2,X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_2])).

cnf(c_176,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_1148,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_26])).

cnf(c_1149,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_1153,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_27,c_25])).

cnf(c_2839,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | r2_hidden(X1_55,X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_1153])).

cnf(c_3380,plain,
    ( ~ m1_connsp_2(X0_55,sK6,k4_yellow_6(sK6,sK7))
    | r2_hidden(k4_yellow_6(sK6,sK7),X0_55)
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_3532,plain,
    ( ~ m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
    | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3380])).

cnf(c_3533,plain,
    ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) != iProver_top
    | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3532])).

cnf(c_3397,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_3400,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3397])).

cnf(c_1748,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k4_yellow_6(sK6,sK7) != X0
    | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1001])).

cnf(c_1749,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1748])).

cnf(c_1750,plain,
    ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_14,plain,
    ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_653,plain,
    ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_654,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_658,plain,
    ( v2_struct_0(X0)
    | m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_24,c_23])).

cnf(c_659,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_860,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_842,c_659])).

cnf(c_1017,plain,
    ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
    | ~ l1_waybel_0(sK7,X0)
    | r2_hidden(X1,k10_yellow_6(X0,sK7))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_860,c_26])).

cnf(c_1018,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_1022,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
    | r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_27,c_25,c_20])).

cnf(c_1737,plain,
    ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | k4_yellow_6(sK6,sK7) != X0
    | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1022])).

cnf(c_1738,plain,
    ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
    | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1737])).

cnf(c_1739,plain,
    ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) = iProver_top
    | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4321,c_3533,c_3400,c_1750,c_1739,c_1464])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:23:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.33/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/0.97  
% 2.33/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.97  
% 2.33/0.97  ------  iProver source info
% 2.33/0.97  
% 2.33/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.97  git: non_committed_changes: false
% 2.33/0.97  git: last_make_outside_of_git: false
% 2.33/0.97  
% 2.33/0.97  ------ 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options
% 2.33/0.97  
% 2.33/0.97  --out_options                           all
% 2.33/0.97  --tptp_safe_out                         true
% 2.33/0.97  --problem_path                          ""
% 2.33/0.97  --include_path                          ""
% 2.33/0.97  --clausifier                            res/vclausify_rel
% 2.33/0.97  --clausifier_options                    --mode clausify
% 2.33/0.97  --stdin                                 false
% 2.33/0.97  --stats_out                             all
% 2.33/0.97  
% 2.33/0.97  ------ General Options
% 2.33/0.97  
% 2.33/0.97  --fof                                   false
% 2.33/0.97  --time_out_real                         305.
% 2.33/0.97  --time_out_virtual                      -1.
% 2.33/0.97  --symbol_type_check                     false
% 2.33/0.97  --clausify_out                          false
% 2.33/0.97  --sig_cnt_out                           false
% 2.33/0.97  --trig_cnt_out                          false
% 2.33/0.97  --trig_cnt_out_tolerance                1.
% 2.33/0.97  --trig_cnt_out_sk_spl                   false
% 2.33/0.97  --abstr_cl_out                          false
% 2.33/0.97  
% 2.33/0.97  ------ Global Options
% 2.33/0.97  
% 2.33/0.97  --schedule                              default
% 2.33/0.97  --add_important_lit                     false
% 2.33/0.97  --prop_solver_per_cl                    1000
% 2.33/0.97  --min_unsat_core                        false
% 2.33/0.97  --soft_assumptions                      false
% 2.33/0.97  --soft_lemma_size                       3
% 2.33/0.97  --prop_impl_unit_size                   0
% 2.33/0.97  --prop_impl_unit                        []
% 2.33/0.97  --share_sel_clauses                     true
% 2.33/0.97  --reset_solvers                         false
% 2.33/0.97  --bc_imp_inh                            [conj_cone]
% 2.33/0.97  --conj_cone_tolerance                   3.
% 2.33/0.97  --extra_neg_conj                        none
% 2.33/0.97  --large_theory_mode                     true
% 2.33/0.97  --prolific_symb_bound                   200
% 2.33/0.97  --lt_threshold                          2000
% 2.33/0.97  --clause_weak_htbl                      true
% 2.33/0.97  --gc_record_bc_elim                     false
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing Options
% 2.33/0.97  
% 2.33/0.97  --preprocessing_flag                    true
% 2.33/0.97  --time_out_prep_mult                    0.1
% 2.33/0.97  --splitting_mode                        input
% 2.33/0.97  --splitting_grd                         true
% 2.33/0.97  --splitting_cvd                         false
% 2.33/0.97  --splitting_cvd_svl                     false
% 2.33/0.97  --splitting_nvd                         32
% 2.33/0.97  --sub_typing                            true
% 2.33/0.97  --prep_gs_sim                           true
% 2.33/0.97  --prep_unflatten                        true
% 2.33/0.97  --prep_res_sim                          true
% 2.33/0.97  --prep_upred                            true
% 2.33/0.97  --prep_sem_filter                       exhaustive
% 2.33/0.97  --prep_sem_filter_out                   false
% 2.33/0.97  --pred_elim                             true
% 2.33/0.97  --res_sim_input                         true
% 2.33/0.97  --eq_ax_congr_red                       true
% 2.33/0.97  --pure_diseq_elim                       true
% 2.33/0.97  --brand_transform                       false
% 2.33/0.97  --non_eq_to_eq                          false
% 2.33/0.97  --prep_def_merge                        true
% 2.33/0.97  --prep_def_merge_prop_impl              false
% 2.33/0.97  --prep_def_merge_mbd                    true
% 2.33/0.97  --prep_def_merge_tr_red                 false
% 2.33/0.97  --prep_def_merge_tr_cl                  false
% 2.33/0.97  --smt_preprocessing                     true
% 2.33/0.97  --smt_ac_axioms                         fast
% 2.33/0.97  --preprocessed_out                      false
% 2.33/0.97  --preprocessed_stats                    false
% 2.33/0.97  
% 2.33/0.97  ------ Abstraction refinement Options
% 2.33/0.97  
% 2.33/0.97  --abstr_ref                             []
% 2.33/0.97  --abstr_ref_prep                        false
% 2.33/0.97  --abstr_ref_until_sat                   false
% 2.33/0.97  --abstr_ref_sig_restrict                funpre
% 2.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.97  --abstr_ref_under                       []
% 2.33/0.97  
% 2.33/0.97  ------ SAT Options
% 2.33/0.97  
% 2.33/0.97  --sat_mode                              false
% 2.33/0.97  --sat_fm_restart_options                ""
% 2.33/0.97  --sat_gr_def                            false
% 2.33/0.97  --sat_epr_types                         true
% 2.33/0.97  --sat_non_cyclic_types                  false
% 2.33/0.97  --sat_finite_models                     false
% 2.33/0.97  --sat_fm_lemmas                         false
% 2.33/0.97  --sat_fm_prep                           false
% 2.33/0.97  --sat_fm_uc_incr                        true
% 2.33/0.97  --sat_out_model                         small
% 2.33/0.97  --sat_out_clauses                       false
% 2.33/0.97  
% 2.33/0.97  ------ QBF Options
% 2.33/0.97  
% 2.33/0.97  --qbf_mode                              false
% 2.33/0.97  --qbf_elim_univ                         false
% 2.33/0.97  --qbf_dom_inst                          none
% 2.33/0.97  --qbf_dom_pre_inst                      false
% 2.33/0.97  --qbf_sk_in                             false
% 2.33/0.97  --qbf_pred_elim                         true
% 2.33/0.97  --qbf_split                             512
% 2.33/0.97  
% 2.33/0.97  ------ BMC1 Options
% 2.33/0.97  
% 2.33/0.97  --bmc1_incremental                      false
% 2.33/0.97  --bmc1_axioms                           reachable_all
% 2.33/0.97  --bmc1_min_bound                        0
% 2.33/0.97  --bmc1_max_bound                        -1
% 2.33/0.97  --bmc1_max_bound_default                -1
% 2.33/0.97  --bmc1_symbol_reachability              true
% 2.33/0.97  --bmc1_property_lemmas                  false
% 2.33/0.97  --bmc1_k_induction                      false
% 2.33/0.97  --bmc1_non_equiv_states                 false
% 2.33/0.97  --bmc1_deadlock                         false
% 2.33/0.97  --bmc1_ucm                              false
% 2.33/0.97  --bmc1_add_unsat_core                   none
% 2.33/0.97  --bmc1_unsat_core_children              false
% 2.33/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.97  --bmc1_out_stat                         full
% 2.33/0.97  --bmc1_ground_init                      false
% 2.33/0.97  --bmc1_pre_inst_next_state              false
% 2.33/0.97  --bmc1_pre_inst_state                   false
% 2.33/0.97  --bmc1_pre_inst_reach_state             false
% 2.33/0.97  --bmc1_out_unsat_core                   false
% 2.33/0.97  --bmc1_aig_witness_out                  false
% 2.33/0.97  --bmc1_verbose                          false
% 2.33/0.97  --bmc1_dump_clauses_tptp                false
% 2.33/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.97  --bmc1_dump_file                        -
% 2.33/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.97  --bmc1_ucm_extend_mode                  1
% 2.33/0.97  --bmc1_ucm_init_mode                    2
% 2.33/0.97  --bmc1_ucm_cone_mode                    none
% 2.33/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.97  --bmc1_ucm_relax_model                  4
% 2.33/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.97  --bmc1_ucm_layered_model                none
% 2.33/0.97  --bmc1_ucm_max_lemma_size               10
% 2.33/0.97  
% 2.33/0.97  ------ AIG Options
% 2.33/0.97  
% 2.33/0.97  --aig_mode                              false
% 2.33/0.97  
% 2.33/0.97  ------ Instantiation Options
% 2.33/0.97  
% 2.33/0.97  --instantiation_flag                    true
% 2.33/0.97  --inst_sos_flag                         false
% 2.33/0.97  --inst_sos_phase                        true
% 2.33/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.97  --inst_lit_sel_side                     num_symb
% 2.33/0.97  --inst_solver_per_active                1400
% 2.33/0.97  --inst_solver_calls_frac                1.
% 2.33/0.97  --inst_passive_queue_type               priority_queues
% 2.33/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.97  --inst_passive_queues_freq              [25;2]
% 2.33/0.97  --inst_dismatching                      true
% 2.33/0.97  --inst_eager_unprocessed_to_passive     true
% 2.33/0.97  --inst_prop_sim_given                   true
% 2.33/0.97  --inst_prop_sim_new                     false
% 2.33/0.97  --inst_subs_new                         false
% 2.33/0.97  --inst_eq_res_simp                      false
% 2.33/0.97  --inst_subs_given                       false
% 2.33/0.97  --inst_orphan_elimination               true
% 2.33/0.97  --inst_learning_loop_flag               true
% 2.33/0.97  --inst_learning_start                   3000
% 2.33/0.97  --inst_learning_factor                  2
% 2.33/0.97  --inst_start_prop_sim_after_learn       3
% 2.33/0.97  --inst_sel_renew                        solver
% 2.33/0.97  --inst_lit_activity_flag                true
% 2.33/0.97  --inst_restr_to_given                   false
% 2.33/0.97  --inst_activity_threshold               500
% 2.33/0.97  --inst_out_proof                        true
% 2.33/0.97  
% 2.33/0.97  ------ Resolution Options
% 2.33/0.97  
% 2.33/0.97  --resolution_flag                       true
% 2.33/0.97  --res_lit_sel                           adaptive
% 2.33/0.97  --res_lit_sel_side                      none
% 2.33/0.97  --res_ordering                          kbo
% 2.33/0.97  --res_to_prop_solver                    active
% 2.33/0.97  --res_prop_simpl_new                    false
% 2.33/0.97  --res_prop_simpl_given                  true
% 2.33/0.97  --res_passive_queue_type                priority_queues
% 2.33/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.97  --res_passive_queues_freq               [15;5]
% 2.33/0.97  --res_forward_subs                      full
% 2.33/0.97  --res_backward_subs                     full
% 2.33/0.97  --res_forward_subs_resolution           true
% 2.33/0.97  --res_backward_subs_resolution          true
% 2.33/0.97  --res_orphan_elimination                true
% 2.33/0.97  --res_time_limit                        2.
% 2.33/0.97  --res_out_proof                         true
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Options
% 2.33/0.97  
% 2.33/0.97  --superposition_flag                    true
% 2.33/0.97  --sup_passive_queue_type                priority_queues
% 2.33/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.97  --demod_completeness_check              fast
% 2.33/0.97  --demod_use_ground                      true
% 2.33/0.97  --sup_to_prop_solver                    passive
% 2.33/0.97  --sup_prop_simpl_new                    true
% 2.33/0.97  --sup_prop_simpl_given                  true
% 2.33/0.97  --sup_fun_splitting                     false
% 2.33/0.97  --sup_smt_interval                      50000
% 2.33/0.97  
% 2.33/0.97  ------ Superposition Simplification Setup
% 2.33/0.97  
% 2.33/0.97  --sup_indices_passive                   []
% 2.33/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_full_bw                           [BwDemod]
% 2.33/0.97  --sup_immed_triv                        [TrivRules]
% 2.33/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_immed_bw_main                     []
% 2.33/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.97  
% 2.33/0.97  ------ Combination Options
% 2.33/0.97  
% 2.33/0.97  --comb_res_mult                         3
% 2.33/0.97  --comb_sup_mult                         2
% 2.33/0.97  --comb_inst_mult                        10
% 2.33/0.97  
% 2.33/0.97  ------ Debug Options
% 2.33/0.97  
% 2.33/0.97  --dbg_backtrace                         false
% 2.33/0.97  --dbg_dump_prop_clauses                 false
% 2.33/0.97  --dbg_dump_prop_clauses_file            -
% 2.33/0.97  --dbg_out_stat                          false
% 2.33/0.97  ------ Parsing...
% 2.33/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.97  ------ Proving...
% 2.33/0.97  ------ Problem Properties 
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  clauses                                 18
% 2.33/0.97  conjectures                             1
% 2.33/0.97  EPR                                     0
% 2.33/0.97  Horn                                    12
% 2.33/0.97  unary                                   4
% 2.33/0.97  binary                                  2
% 2.33/0.97  lits                                    50
% 2.33/0.97  lits eq                                 5
% 2.33/0.97  fd_pure                                 0
% 2.33/0.97  fd_pseudo                               0
% 2.33/0.97  fd_cond                                 4
% 2.33/0.97  fd_pseudo_cond                          0
% 2.33/0.97  AC symbols                              0
% 2.33/0.97  
% 2.33/0.97  ------ Schedule dynamic 5 is on 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.97  
% 2.33/0.97  
% 2.33/0.97  ------ 
% 2.33/0.97  Current options:
% 2.33/0.97  ------ 
% 2.33/0.97  
% 2.33/0.97  ------ Input Options
% 2.33/0.97  
% 2.33/0.97  --out_options                           all
% 2.33/0.97  --tptp_safe_out                         true
% 2.33/0.97  --problem_path                          ""
% 2.33/0.97  --include_path                          ""
% 2.33/0.97  --clausifier                            res/vclausify_rel
% 2.33/0.97  --clausifier_options                    --mode clausify
% 2.33/0.97  --stdin                                 false
% 2.33/0.97  --stats_out                             all
% 2.33/0.97  
% 2.33/0.97  ------ General Options
% 2.33/0.97  
% 2.33/0.97  --fof                                   false
% 2.33/0.97  --time_out_real                         305.
% 2.33/0.97  --time_out_virtual                      -1.
% 2.33/0.97  --symbol_type_check                     false
% 2.33/0.97  --clausify_out                          false
% 2.33/0.97  --sig_cnt_out                           false
% 2.33/0.97  --trig_cnt_out                          false
% 2.33/0.97  --trig_cnt_out_tolerance                1.
% 2.33/0.97  --trig_cnt_out_sk_spl                   false
% 2.33/0.97  --abstr_cl_out                          false
% 2.33/0.97  
% 2.33/0.97  ------ Global Options
% 2.33/0.97  
% 2.33/0.97  --schedule                              default
% 2.33/0.97  --add_important_lit                     false
% 2.33/0.97  --prop_solver_per_cl                    1000
% 2.33/0.97  --min_unsat_core                        false
% 2.33/0.97  --soft_assumptions                      false
% 2.33/0.97  --soft_lemma_size                       3
% 2.33/0.97  --prop_impl_unit_size                   0
% 2.33/0.97  --prop_impl_unit                        []
% 2.33/0.97  --share_sel_clauses                     true
% 2.33/0.97  --reset_solvers                         false
% 2.33/0.97  --bc_imp_inh                            [conj_cone]
% 2.33/0.97  --conj_cone_tolerance                   3.
% 2.33/0.97  --extra_neg_conj                        none
% 2.33/0.97  --large_theory_mode                     true
% 2.33/0.97  --prolific_symb_bound                   200
% 2.33/0.97  --lt_threshold                          2000
% 2.33/0.97  --clause_weak_htbl                      true
% 2.33/0.97  --gc_record_bc_elim                     false
% 2.33/0.97  
% 2.33/0.97  ------ Preprocessing Options
% 2.33/0.97  
% 2.33/0.97  --preprocessing_flag                    true
% 2.33/0.97  --time_out_prep_mult                    0.1
% 2.33/0.97  --splitting_mode                        input
% 2.33/0.97  --splitting_grd                         true
% 2.33/0.97  --splitting_cvd                         false
% 2.33/0.97  --splitting_cvd_svl                     false
% 2.33/0.97  --splitting_nvd                         32
% 2.33/0.97  --sub_typing                            true
% 2.33/0.97  --prep_gs_sim                           true
% 2.33/0.97  --prep_unflatten                        true
% 2.33/0.97  --prep_res_sim                          true
% 2.33/0.97  --prep_upred                            true
% 2.33/0.97  --prep_sem_filter                       exhaustive
% 2.33/0.97  --prep_sem_filter_out                   false
% 2.33/0.97  --pred_elim                             true
% 2.33/0.97  --res_sim_input                         true
% 2.33/0.97  --eq_ax_congr_red                       true
% 2.33/0.97  --pure_diseq_elim                       true
% 2.33/0.97  --brand_transform                       false
% 2.33/0.97  --non_eq_to_eq                          false
% 2.33/0.97  --prep_def_merge                        true
% 2.33/0.97  --prep_def_merge_prop_impl              false
% 2.33/0.97  --prep_def_merge_mbd                    true
% 2.33/0.97  --prep_def_merge_tr_red                 false
% 2.33/0.97  --prep_def_merge_tr_cl                  false
% 2.33/0.97  --smt_preprocessing                     true
% 2.33/0.97  --smt_ac_axioms                         fast
% 2.33/0.97  --preprocessed_out                      false
% 2.33/0.97  --preprocessed_stats                    false
% 2.33/0.97  
% 2.33/0.97  ------ Abstraction refinement Options
% 2.33/0.97  
% 2.33/0.97  --abstr_ref                             []
% 2.33/0.97  --abstr_ref_prep                        false
% 2.33/0.97  --abstr_ref_until_sat                   false
% 2.33/0.97  --abstr_ref_sig_restrict                funpre
% 2.33/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.97  --abstr_ref_under                       []
% 2.33/0.97  
% 2.33/0.97  ------ SAT Options
% 2.33/0.97  
% 2.33/0.97  --sat_mode                              false
% 2.33/0.97  --sat_fm_restart_options                ""
% 2.33/0.97  --sat_gr_def                            false
% 2.33/0.97  --sat_epr_types                         true
% 2.33/0.97  --sat_non_cyclic_types                  false
% 2.33/0.97  --sat_finite_models                     false
% 2.33/0.97  --sat_fm_lemmas                         false
% 2.33/0.97  --sat_fm_prep                           false
% 2.33/0.97  --sat_fm_uc_incr                        true
% 2.33/0.97  --sat_out_model                         small
% 2.33/0.97  --sat_out_clauses                       false
% 2.33/0.97  
% 2.33/0.97  ------ QBF Options
% 2.33/0.97  
% 2.33/0.97  --qbf_mode                              false
% 2.33/0.97  --qbf_elim_univ                         false
% 2.33/0.97  --qbf_dom_inst                          none
% 2.33/0.97  --qbf_dom_pre_inst                      false
% 2.33/0.97  --qbf_sk_in                             false
% 2.33/0.97  --qbf_pred_elim                         true
% 2.33/0.97  --qbf_split                             512
% 2.33/0.97  
% 2.33/0.97  ------ BMC1 Options
% 2.33/0.97  
% 2.33/0.97  --bmc1_incremental                      false
% 2.33/0.97  --bmc1_axioms                           reachable_all
% 2.33/0.97  --bmc1_min_bound                        0
% 2.33/0.97  --bmc1_max_bound                        -1
% 2.33/0.97  --bmc1_max_bound_default                -1
% 2.33/0.98  --bmc1_symbol_reachability              true
% 2.33/0.98  --bmc1_property_lemmas                  false
% 2.33/0.98  --bmc1_k_induction                      false
% 2.33/0.98  --bmc1_non_equiv_states                 false
% 2.33/0.98  --bmc1_deadlock                         false
% 2.33/0.98  --bmc1_ucm                              false
% 2.33/0.98  --bmc1_add_unsat_core                   none
% 2.33/0.98  --bmc1_unsat_core_children              false
% 2.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.98  --bmc1_out_stat                         full
% 2.33/0.98  --bmc1_ground_init                      false
% 2.33/0.98  --bmc1_pre_inst_next_state              false
% 2.33/0.98  --bmc1_pre_inst_state                   false
% 2.33/0.98  --bmc1_pre_inst_reach_state             false
% 2.33/0.98  --bmc1_out_unsat_core                   false
% 2.33/0.98  --bmc1_aig_witness_out                  false
% 2.33/0.98  --bmc1_verbose                          false
% 2.33/0.98  --bmc1_dump_clauses_tptp                false
% 2.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.98  --bmc1_dump_file                        -
% 2.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.98  --bmc1_ucm_extend_mode                  1
% 2.33/0.98  --bmc1_ucm_init_mode                    2
% 2.33/0.98  --bmc1_ucm_cone_mode                    none
% 2.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.98  --bmc1_ucm_relax_model                  4
% 2.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.98  --bmc1_ucm_layered_model                none
% 2.33/0.98  --bmc1_ucm_max_lemma_size               10
% 2.33/0.98  
% 2.33/0.98  ------ AIG Options
% 2.33/0.98  
% 2.33/0.98  --aig_mode                              false
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation Options
% 2.33/0.98  
% 2.33/0.98  --instantiation_flag                    true
% 2.33/0.98  --inst_sos_flag                         false
% 2.33/0.98  --inst_sos_phase                        true
% 2.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel_side                     none
% 2.33/0.98  --inst_solver_per_active                1400
% 2.33/0.98  --inst_solver_calls_frac                1.
% 2.33/0.98  --inst_passive_queue_type               priority_queues
% 2.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.98  --inst_passive_queues_freq              [25;2]
% 2.33/0.98  --inst_dismatching                      true
% 2.33/0.98  --inst_eager_unprocessed_to_passive     true
% 2.33/0.98  --inst_prop_sim_given                   true
% 2.33/0.98  --inst_prop_sim_new                     false
% 2.33/0.98  --inst_subs_new                         false
% 2.33/0.98  --inst_eq_res_simp                      false
% 2.33/0.98  --inst_subs_given                       false
% 2.33/0.98  --inst_orphan_elimination               true
% 2.33/0.98  --inst_learning_loop_flag               true
% 2.33/0.98  --inst_learning_start                   3000
% 2.33/0.98  --inst_learning_factor                  2
% 2.33/0.98  --inst_start_prop_sim_after_learn       3
% 2.33/0.98  --inst_sel_renew                        solver
% 2.33/0.98  --inst_lit_activity_flag                true
% 2.33/0.98  --inst_restr_to_given                   false
% 2.33/0.98  --inst_activity_threshold               500
% 2.33/0.98  --inst_out_proof                        true
% 2.33/0.98  
% 2.33/0.98  ------ Resolution Options
% 2.33/0.98  
% 2.33/0.98  --resolution_flag                       false
% 2.33/0.98  --res_lit_sel                           adaptive
% 2.33/0.98  --res_lit_sel_side                      none
% 2.33/0.98  --res_ordering                          kbo
% 2.33/0.98  --res_to_prop_solver                    active
% 2.33/0.98  --res_prop_simpl_new                    false
% 2.33/0.98  --res_prop_simpl_given                  true
% 2.33/0.98  --res_passive_queue_type                priority_queues
% 2.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.98  --res_passive_queues_freq               [15;5]
% 2.33/0.98  --res_forward_subs                      full
% 2.33/0.98  --res_backward_subs                     full
% 2.33/0.98  --res_forward_subs_resolution           true
% 2.33/0.98  --res_backward_subs_resolution          true
% 2.33/0.98  --res_orphan_elimination                true
% 2.33/0.98  --res_time_limit                        2.
% 2.33/0.98  --res_out_proof                         true
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Options
% 2.33/0.98  
% 2.33/0.98  --superposition_flag                    true
% 2.33/0.98  --sup_passive_queue_type                priority_queues
% 2.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.98  --demod_completeness_check              fast
% 2.33/0.98  --demod_use_ground                      true
% 2.33/0.98  --sup_to_prop_solver                    passive
% 2.33/0.98  --sup_prop_simpl_new                    true
% 2.33/0.98  --sup_prop_simpl_given                  true
% 2.33/0.98  --sup_fun_splitting                     false
% 2.33/0.98  --sup_smt_interval                      50000
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Simplification Setup
% 2.33/0.98  
% 2.33/0.98  --sup_indices_passive                   []
% 2.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_full_bw                           [BwDemod]
% 2.33/0.98  --sup_immed_triv                        [TrivRules]
% 2.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_immed_bw_main                     []
% 2.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  
% 2.33/0.98  ------ Combination Options
% 2.33/0.98  
% 2.33/0.98  --comb_res_mult                         3
% 2.33/0.98  --comb_sup_mult                         2
% 2.33/0.98  --comb_inst_mult                        10
% 2.33/0.98  
% 2.33/0.98  ------ Debug Options
% 2.33/0.98  
% 2.33/0.98  --dbg_backtrace                         false
% 2.33/0.98  --dbg_dump_prop_clauses                 false
% 2.33/0.98  --dbg_dump_prop_clauses_file            -
% 2.33/0.98  --dbg_out_stat                          false
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  ------ Proving...
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  % SZS status Theorem for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  fof(f1,axiom,(
% 2.33/0.98    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f29,plain,(
% 2.33/0.98    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f30,plain,(
% 2.33/0.98    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f29])).
% 2.33/0.98  
% 2.33/0.98  fof(f46,plain,(
% 2.33/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f30])).
% 2.33/0.98  
% 2.33/0.98  fof(f10,conjecture,(
% 2.33/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f11,negated_conjecture,(
% 2.33/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1))))),
% 2.33/0.98    inference(negated_conjecture,[],[f10])).
% 2.33/0.98  
% 2.33/0.98  fof(f27,plain,(
% 2.33/0.98    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & (l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f11])).
% 2.33/0.98  
% 2.33/0.98  fof(f28,plain,(
% 2.33/0.98    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f27])).
% 2.33/0.98  
% 2.33/0.98  fof(f44,plain,(
% 2.33/0.98    ( ! [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r2_hidden(k4_yellow_6(X0,sK7),k10_yellow_6(X0,sK7)) & l1_waybel_0(sK7,X0) & v1_yellow_6(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f43,plain,(
% 2.33/0.98    ? [X0] : (? [X1] : (~r2_hidden(k4_yellow_6(X0,X1),k10_yellow_6(X0,X1)) & l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r2_hidden(k4_yellow_6(sK6,X1),k10_yellow_6(sK6,X1)) & l1_waybel_0(X1,sK6) & v1_yellow_6(X1,sK6) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f45,plain,(
% 2.33/0.98    (~r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) & l1_waybel_0(sK7,sK6) & v1_yellow_6(sK7,sK6) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f28,f44,f43])).
% 2.33/0.98  
% 2.33/0.98  fof(f72,plain,(
% 2.33/0.98    l1_waybel_0(sK7,sK6)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f2,axiom,(
% 2.33/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f12,plain,(
% 2.33/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.33/0.98    inference(ennf_transformation,[],[f2])).
% 2.33/0.98  
% 2.33/0.98  fof(f47,plain,(
% 2.33/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f12])).
% 2.33/0.98  
% 2.33/0.98  fof(f5,axiom,(
% 2.33/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f17,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f5])).
% 2.33/0.98  
% 2.33/0.98  fof(f18,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f17])).
% 2.33/0.98  
% 2.33/0.98  fof(f31,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(nnf_transformation,[],[f18])).
% 2.33/0.98  
% 2.33/0.98  fof(f32,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(rectify,[],[f31])).
% 2.33/0.98  
% 2.33/0.98  fof(f34,plain,(
% 2.33/0.98    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f33,plain,(
% 2.33/0.98    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f35,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f34,f33])).
% 2.33/0.98  
% 2.33/0.98  fof(f52,plain,(
% 2.33/0.98    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f67,plain,(
% 2.33/0.98    l1_pre_topc(sK6)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f65,plain,(
% 2.33/0.98    ~v2_struct_0(sK6)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f68,plain,(
% 2.33/0.98    ~v2_struct_0(sK7)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f9,axiom,(
% 2.33/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f25,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f9])).
% 2.33/0.98  
% 2.33/0.98  fof(f26,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f25])).
% 2.33/0.98  
% 2.33/0.98  fof(f64,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k4_yellow_6(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v1_yellow_6(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f26])).
% 2.33/0.98  
% 2.33/0.98  fof(f71,plain,(
% 2.33/0.98    v1_yellow_6(sK7,sK6)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f69,plain,(
% 2.33/0.98    v4_orders_2(sK7)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f70,plain,(
% 2.33/0.98    v7_waybel_0(sK7)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f7,axiom,(
% 2.33/0.98    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f21,plain,(
% 2.33/0.98    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f7])).
% 2.33/0.98  
% 2.33/0.98  fof(f22,plain,(
% 2.33/0.98    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f21])).
% 2.33/0.98  
% 2.33/0.98  fof(f62,plain,(
% 2.33/0.98    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f22])).
% 2.33/0.98  
% 2.33/0.98  fof(f6,axiom,(
% 2.33/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f19,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f6])).
% 2.33/0.98  
% 2.33/0.98  fof(f20,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f19])).
% 2.33/0.98  
% 2.33/0.98  fof(f36,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(nnf_transformation,[],[f20])).
% 2.33/0.98  
% 2.33/0.98  fof(f37,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f36])).
% 2.33/0.98  
% 2.33/0.98  fof(f38,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(rectify,[],[f37])).
% 2.33/0.98  
% 2.33/0.98  fof(f41,plain,(
% 2.33/0.98    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) & m1_connsp_2(sK5(X0,X1,X6),X0,X6)))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f40,plain,(
% 2.33/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,X3)))) )),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f39,plain,(
% 2.33/0.98    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK3(X0,X1,X2))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK3(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f42,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK3(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) & m1_connsp_2(sK5(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f57,plain,(
% 2.33/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f42])).
% 2.33/0.98  
% 2.33/0.98  fof(f74,plain,(
% 2.33/0.98    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK5(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(equality_resolution,[],[f57])).
% 2.33/0.98  
% 2.33/0.98  fof(f66,plain,(
% 2.33/0.98    v2_pre_topc(sK6)),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f73,plain,(
% 2.33/0.98    ~r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7))),
% 2.33/0.98    inference(cnf_transformation,[],[f45])).
% 2.33/0.98  
% 2.33/0.98  fof(f8,axiom,(
% 2.33/0.98    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f23,plain,(
% 2.33/0.98    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f8])).
% 2.33/0.98  
% 2.33/0.98  fof(f24,plain,(
% 2.33/0.98    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f23])).
% 2.33/0.98  
% 2.33/0.98  fof(f63,plain,(
% 2.33/0.98    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f24])).
% 2.33/0.98  
% 2.33/0.98  fof(f54,plain,(
% 2.33/0.98    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f4,axiom,(
% 2.33/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f15,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f4])).
% 2.33/0.98  
% 2.33/0.98  fof(f16,plain,(
% 2.33/0.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f15])).
% 2.33/0.98  
% 2.33/0.98  fof(f49,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f16])).
% 2.33/0.98  
% 2.33/0.98  fof(f3,axiom,(
% 2.33/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f13,plain,(
% 2.33/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f3])).
% 2.33/0.98  
% 2.33/0.98  fof(f14,plain,(
% 2.33/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.33/0.98    inference(flattening,[],[f13])).
% 2.33/0.98  
% 2.33/0.98  fof(f48,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f14])).
% 2.33/0.98  
% 2.33/0.98  fof(f56,plain,(
% 2.33/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK5(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f42])).
% 2.33/0.98  
% 2.33/0.98  fof(f75,plain,(
% 2.33/0.98    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK5(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.33/0.98    inference(equality_resolution,[],[f56])).
% 2.33/0.98  
% 2.33/0.98  cnf(c_0,plain,
% 2.33/0.98      ( m1_subset_1(sK0(X0),X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2850,plain,
% 2.33/0.98      ( m1_subset_1(sK0(X0_56),X0_56) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3204,plain,
% 2.33/0.98      ( m1_subset_1(sK0(X0_56),X0_56) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2850]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_20,negated_conjecture,
% 2.33/0.98      ( l1_waybel_0(sK7,sK6) ),
% 2.33/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1,plain,
% 2.33/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_6,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_struct_0(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_401,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_25,negated_conjecture,
% 2.33/0.98      ( l1_pre_topc(sK6) ),
% 2.33/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1258,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | sK6 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_401,c_25]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1259,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1258]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_27,negated_conjecture,
% 2.33/0.98      ( ~ v2_struct_0(sK6) ),
% 2.33/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1263,plain,
% 2.33/0.98      ( v2_struct_0(X0)
% 2.33/0.98      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | r1_waybel_0(sK6,X0,X1) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1259,c_27]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1264,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_1263]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1487,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | m1_subset_1(sK1(sK6,X0,X1,X2),u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | sK7 != X0
% 2.33/0.98      | sK6 != sK6 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_1264]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1488,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.33/0.98      | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
% 2.33/0.98      | v2_struct_0(sK7) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1487]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_24,negated_conjecture,
% 2.33/0.98      ( ~ v2_struct_0(sK7) ),
% 2.33/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1492,plain,
% 2.33/0.98      ( m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.33/0.98      | r1_waybel_0(sK6,sK7,X0) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1488,c_24]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1493,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.33/0.98      | m1_subset_1(sK1(sK6,sK7,X0,X1),u1_struct_0(sK7)) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_1492]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2834,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0_55)
% 2.33/0.98      | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 2.33/0.98      | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_1493]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3220,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.33/0.98      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top
% 2.33/0.98      | m1_subset_1(sK1(sK6,sK7,X0_55,X1_55),u1_struct_0(sK7)) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2834]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_18,plain,
% 2.33/0.98      ( ~ v1_yellow_6(X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ v4_orders_2(X0)
% 2.33/0.98      | ~ v7_waybel_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ l1_struct_0(X1)
% 2.33/0.98      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_21,negated_conjecture,
% 2.33/0.98      ( v1_yellow_6(sK7,sK6) ),
% 2.33/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_316,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ v4_orders_2(X0)
% 2.33/0.98      | ~ v7_waybel_0(X0)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_struct_0(X1)
% 2.33/0.98      | k2_waybel_0(X1,X0,X2) = k4_yellow_6(X1,X0)
% 2.33/0.98      | sK7 != X0
% 2.33/0.98      | sK6 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_317,plain,
% 2.33/0.98      ( ~ l1_waybel_0(sK7,sK6)
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.33/0.98      | ~ v4_orders_2(sK7)
% 2.33/0.98      | ~ v7_waybel_0(sK7)
% 2.33/0.98      | v2_struct_0(sK7)
% 2.33/0.98      | v2_struct_0(sK6)
% 2.33/0.98      | ~ l1_struct_0(sK6)
% 2.33/0.98      | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_316]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_23,negated_conjecture,
% 2.33/0.98      ( v4_orders_2(sK7) ),
% 2.33/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_22,negated_conjecture,
% 2.33/0.98      ( v7_waybel_0(sK7) ),
% 2.33/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_89,plain,
% 2.33/0.98      ( ~ l1_pre_topc(sK6) | l1_struct_0(sK6) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_321,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.33/0.98      | k2_waybel_0(sK6,sK7,X0) = k4_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_317,c_27,c_25,c_24,c_23,c_22,c_20,c_89]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2848,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 2.33/0.98      | k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_321]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3206,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,X0_55) = k4_yellow_6(sK6,sK7)
% 2.33/0.98      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2848]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3809,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)) = k4_yellow_6(sK6,sK7)
% 2.33/0.98      | r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.33/0.98      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_3220,c_3206]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4099,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.33/0.98      | r1_waybel_0(sK6,sK7,X0_55) = iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_3204,c_3809]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_16,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/0.98      | ~ v4_orders_2(X0)
% 2.33/0.98      | ~ v7_waybel_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_836,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/0.98      | ~ v4_orders_2(X0)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1)
% 2.33/0.98      | sK7 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_837,plain,
% 2.33/0.98      ( ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(sK7)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(sK7)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_836]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_841,plain,
% 2.33/0.98      ( v2_struct_0(X0)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_837,c_24,c_23]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_842,plain,
% 2.33/0.98      ( ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_841]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_13,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(X1)
% 2.33/0.98      | ~ v7_waybel_0(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_689,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X2))
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0)
% 2.33/0.98      | sK7 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_690,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(sK7)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(sK7)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_689]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_694,plain,
% 2.33/0.98      ( v2_struct_0(X0)
% 2.33/0.98      | ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_690,c_24,c_23]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_695,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_694]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_861,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(backward_subsumption_resolution,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_842,c_695]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_26,negated_conjecture,
% 2.33/0.98      ( v2_pre_topc(sK6) ),
% 2.33/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_996,plain,
% 2.33/0.98      ( ~ r1_waybel_0(X0,sK7,sK5(X0,sK7,X1))
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0)
% 2.33/0.98      | sK6 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_861,c_26]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_997,plain,
% 2.33/0.98      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.33/0.98      | ~ l1_waybel_0(sK7,sK6)
% 2.33/0.98      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.33/0.98      | v2_struct_0(sK6)
% 2.33/0.98      | ~ l1_pre_topc(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_996]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1001,plain,
% 2.33/0.98      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.33/0.98      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_997,c_27,c_25,c_20]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2846,plain,
% 2.33/0.98      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55))
% 2.33/0.98      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_1001]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3208,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0_55)) != iProver_top
% 2.33/0.98      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.33/0.98      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4130,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,X0_55),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.33/0.98      | r2_hidden(X0_55,k10_yellow_6(sK6,sK7)) = iProver_top
% 2.33/0.98      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_4099,c_3208]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_19,negated_conjecture,
% 2.33/0.98      ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
% 2.33/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2849,negated_conjecture,
% 2.33/0.98      ( ~ r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3205,plain,
% 2.33/0.98      ( r2_hidden(k4_yellow_6(sK6,sK7),k10_yellow_6(sK6,sK7)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4222,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_4130,c_3205]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_17,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_struct_0(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_480,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_pre_topc(X2)
% 2.33/0.98      | X1 != X2 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_481,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_480]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1333,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,X1)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(X1,X0),u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | sK6 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_481,c_25]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1334,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
% 2.33/0.98      | v2_struct_0(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1333]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1338,plain,
% 2.33/0.98      ( m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1334,c_27]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1339,plain,
% 2.33/0.98      ( ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_1338]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1462,plain,
% 2.33/0.98      ( m1_subset_1(k4_yellow_6(sK6,X0),u1_struct_0(sK6))
% 2.33/0.98      | sK7 != X0
% 2.33/0.98      | sK6 != sK6 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_1339]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1463,plain,
% 2.33/0.98      ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1462]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1464,plain,
% 2.33/0.98      ( m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4318,plain,
% 2.33/0.98      ( k2_waybel_0(sK6,sK7,sK1(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK0(u1_struct_0(sK7)))) = k4_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_4222,c_1464]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_struct_0(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_427,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1233,plain,
% 2.33/0.98      ( r1_waybel_0(X0,X1,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 2.33/0.98      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | sK6 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_427,c_25]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1234,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1233]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1238,plain,
% 2.33/0.98      ( v2_struct_0(X0)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | r1_waybel_0(sK6,X0,X1) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1234,c_27]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1239,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(X0,sK6)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_1238]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1508,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,X0,X1)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,X0,sK1(sK6,X0,X1,X2)),X1)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | sK7 != X0
% 2.33/0.98      | sK6 != sK6 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_1239]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1509,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.33/0.98      | v2_struct_0(sK7) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1508]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1513,plain,
% 2.33/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.33/0.98      | r1_waybel_0(sK6,sK7,X0) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1509,c_24]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1514,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0,X1)),X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK7)) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_1513]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2833,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0_55)
% 2.33/0.98      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55)
% 2.33/0.98      | ~ m1_subset_1(X1_55,u1_struct_0(sK7)) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_1514]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3221,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,X0_55) = iProver_top
% 2.33/0.98      | r2_hidden(k2_waybel_0(sK6,sK7,sK1(sK6,sK7,X0_55,X1_55)),X0_55) != iProver_top
% 2.33/0.98      | m1_subset_1(X1_55,u1_struct_0(sK7)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2833]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4321,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
% 2.33/0.98      | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
% 2.33/0.98      | m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_4318,c_3221]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.33/0.98      | r2_hidden(X2,X0)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_175,plain,
% 2.33/0.98      ( r2_hidden(X2,X0)
% 2.33/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3,c_2]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_176,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.33/0.98      | r2_hidden(X2,X0)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_175]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1148,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.33/0.98      | r2_hidden(X2,X0)
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ l1_pre_topc(X1)
% 2.33/0.98      | sK6 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_176,c_26]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1149,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.33/0.98      | r2_hidden(X1,X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 2.33/0.98      | v2_struct_0(sK6)
% 2.33/0.98      | ~ l1_pre_topc(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1148]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1153,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0,sK6,X1)
% 2.33/0.98      | r2_hidden(X1,X0)
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1149,c_27,c_25]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2839,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 2.33/0.98      | r2_hidden(X1_55,X0_55)
% 2.33/0.98      | ~ m1_subset_1(X1_55,u1_struct_0(sK6)) ),
% 2.33/0.98      inference(subtyping,[status(esa)],[c_1153]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3380,plain,
% 2.33/0.98      ( ~ m1_connsp_2(X0_55,sK6,k4_yellow_6(sK6,sK7))
% 2.33/0.98      | r2_hidden(k4_yellow_6(sK6,sK7),X0_55)
% 2.33/0.98      | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_2839]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3532,plain,
% 2.33/0.98      ( ~ m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
% 2.33/0.98      | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
% 2.33/0.98      | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_3380]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3533,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) != iProver_top
% 2.33/0.98      | r2_hidden(k4_yellow_6(sK6,sK7),sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) = iProver_top
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_3532]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3397,plain,
% 2.33/0.98      ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_2850]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3400,plain,
% 2.33/0.98      ( m1_subset_1(sK0(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_3397]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1748,plain,
% 2.33/0.98      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,X0))
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.33/0.98      | k4_yellow_6(sK6,sK7) != X0
% 2.33/0.98      | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_1001]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1749,plain,
% 2.33/0.98      ( ~ r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7)))
% 2.33/0.98      | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1748]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1750,plain,
% 2.33/0.98      ( r1_waybel_0(sK6,sK7,sK5(sK6,sK7,k4_yellow_6(sK6,sK7))) != iProver_top
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_14,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(X1)
% 2.33/0.98      | ~ v7_waybel_0(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_653,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,X1,X2),X0,X2)
% 2.33/0.98      | ~ l1_waybel_0(X1,X0)
% 2.33/0.98      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 2.33/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(X1)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(X1)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0)
% 2.33/0.98      | sK7 != X1 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_654,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v4_orders_2(sK7)
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | v2_struct_0(sK7)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_653]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_658,plain,
% 2.33/0.98      ( v2_struct_0(X0)
% 2.33/0.98      | m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_654,c_24,c_23]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_659,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | ~ m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_658]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_860,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ v2_pre_topc(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0) ),
% 2.33/0.98      inference(backward_subsumption_resolution,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_842,c_659]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1017,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(X0,sK7,X1),X0,X1)
% 2.33/0.98      | ~ l1_waybel_0(sK7,X0)
% 2.33/0.98      | r2_hidden(X1,k10_yellow_6(X0,sK7))
% 2.33/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.33/0.98      | v2_struct_0(X0)
% 2.33/0.98      | ~ l1_pre_topc(X0)
% 2.33/0.98      | sK6 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_860,c_26]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1018,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
% 2.33/0.98      | ~ l1_waybel_0(sK7,sK6)
% 2.33/0.98      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.33/0.98      | v2_struct_0(sK6)
% 2.33/0.98      | ~ l1_pre_topc(sK6) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1017]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1022,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
% 2.33/0.98      | r2_hidden(X0,k10_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_1018,c_27,c_25,c_20]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1737,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,X0),sK6,X0)
% 2.33/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 2.33/0.98      | k4_yellow_6(sK6,sK7) != X0
% 2.33/0.98      | k10_yellow_6(sK6,sK7) != k10_yellow_6(sK6,sK7) ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_1022]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1738,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7))
% 2.33/0.98      | ~ m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_1737]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1739,plain,
% 2.33/0.98      ( m1_connsp_2(sK5(sK6,sK7,k4_yellow_6(sK6,sK7)),sK6,k4_yellow_6(sK6,sK7)) = iProver_top
% 2.33/0.98      | m1_subset_1(k4_yellow_6(sK6,sK7),u1_struct_0(sK6)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(contradiction,plain,
% 2.33/0.98      ( $false ),
% 2.33/0.98      inference(minisat,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_4321,c_3533,c_3400,c_1750,c_1739,c_1464]) ).
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  ------                               Statistics
% 2.33/0.98  
% 2.33/0.98  ------ General
% 2.33/0.98  
% 2.33/0.98  abstr_ref_over_cycles:                  0
% 2.33/0.98  abstr_ref_under_cycles:                 0
% 2.33/0.98  gc_basic_clause_elim:                   0
% 2.33/0.98  forced_gc_time:                         0
% 2.33/0.98  parsing_time:                           0.011
% 2.33/0.98  unif_index_cands_time:                  0.
% 2.33/0.98  unif_index_add_time:                    0.
% 2.33/0.98  orderings_time:                         0.
% 2.33/0.98  out_proof_time:                         0.013
% 2.33/0.98  total_time:                             0.164
% 2.33/0.98  num_of_symbols:                         57
% 2.33/0.98  num_of_terms:                           3366
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing
% 2.33/0.98  
% 2.33/0.98  num_of_splits:                          0
% 2.33/0.98  num_of_split_atoms:                     0
% 2.33/0.98  num_of_reused_defs:                     0
% 2.33/0.98  num_eq_ax_congr_red:                    59
% 2.33/0.98  num_of_sem_filtered_clauses:            1
% 2.33/0.98  num_of_subtypes:                        3
% 2.33/0.98  monotx_restored_types:                  1
% 2.33/0.98  sat_num_of_epr_types:                   0
% 2.33/0.98  sat_num_of_non_cyclic_types:            0
% 2.33/0.98  sat_guarded_non_collapsed_types:        0
% 2.33/0.98  num_pure_diseq_elim:                    0
% 2.33/0.98  simp_replaced_by:                       0
% 2.33/0.98  res_preprocessed:                       99
% 2.33/0.98  prep_upred:                             0
% 2.33/0.98  prep_unflattend:                        149
% 2.33/0.98  smt_new_axioms:                         0
% 2.33/0.98  pred_elim_cands:                        4
% 2.33/0.98  pred_elim:                              9
% 2.33/0.98  pred_elim_cl:                           10
% 2.33/0.98  pred_elim_cycles:                       15
% 2.33/0.98  merged_defs:                            0
% 2.33/0.98  merged_defs_ncl:                        0
% 2.33/0.98  bin_hyper_res:                          0
% 2.33/0.98  prep_cycles:                            4
% 2.33/0.98  pred_elim_time:                         0.052
% 2.33/0.98  splitting_time:                         0.
% 2.33/0.98  sem_filter_time:                        0.
% 2.33/0.98  monotx_time:                            0.
% 2.33/0.98  subtype_inf_time:                       0.001
% 2.33/0.98  
% 2.33/0.98  ------ Problem properties
% 2.33/0.98  
% 2.33/0.98  clauses:                                18
% 2.33/0.98  conjectures:                            1
% 2.33/0.98  epr:                                    0
% 2.33/0.98  horn:                                   12
% 2.33/0.98  ground:                                 3
% 2.33/0.98  unary:                                  4
% 2.33/0.98  binary:                                 2
% 2.33/0.98  lits:                                   50
% 2.33/0.98  lits_eq:                                5
% 2.33/0.98  fd_pure:                                0
% 2.33/0.98  fd_pseudo:                              0
% 2.33/0.98  fd_cond:                                4
% 2.33/0.98  fd_pseudo_cond:                         0
% 2.33/0.98  ac_symbols:                             0
% 2.33/0.98  
% 2.33/0.98  ------ Propositional Solver
% 2.33/0.98  
% 2.33/0.98  prop_solver_calls:                      26
% 2.33/0.98  prop_fast_solver_calls:                 1523
% 2.33/0.98  smt_solver_calls:                       0
% 2.33/0.98  smt_fast_solver_calls:                  0
% 2.33/0.98  prop_num_of_clauses:                    1067
% 2.33/0.98  prop_preprocess_simplified:             3879
% 2.33/0.98  prop_fo_subsumed:                       88
% 2.33/0.98  prop_solver_time:                       0.
% 2.33/0.98  smt_solver_time:                        0.
% 2.33/0.98  smt_fast_solver_time:                   0.
% 2.33/0.98  prop_fast_solver_time:                  0.
% 2.33/0.98  prop_unsat_core_time:                   0.
% 2.33/0.98  
% 2.33/0.98  ------ QBF
% 2.33/0.98  
% 2.33/0.98  qbf_q_res:                              0
% 2.33/0.98  qbf_num_tautologies:                    0
% 2.33/0.98  qbf_prep_cycles:                        0
% 2.33/0.98  
% 2.33/0.98  ------ BMC1
% 2.33/0.98  
% 2.33/0.98  bmc1_current_bound:                     -1
% 2.33/0.98  bmc1_last_solved_bound:                 -1
% 2.33/0.98  bmc1_unsat_core_size:                   -1
% 2.33/0.98  bmc1_unsat_core_parents_size:           -1
% 2.33/0.98  bmc1_merge_next_fun:                    0
% 2.33/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation
% 2.33/0.98  
% 2.33/0.98  inst_num_of_clauses:                    170
% 2.33/0.98  inst_num_in_passive:                    29
% 2.33/0.98  inst_num_in_active:                     124
% 2.33/0.98  inst_num_in_unprocessed:                17
% 2.33/0.98  inst_num_of_loops:                      140
% 2.33/0.98  inst_num_of_learning_restarts:          0
% 2.33/0.98  inst_num_moves_active_passive:          12
% 2.33/0.98  inst_lit_activity:                      0
% 2.33/0.98  inst_lit_activity_moves:                0
% 2.33/0.98  inst_num_tautologies:                   0
% 2.33/0.98  inst_num_prop_implied:                  0
% 2.33/0.98  inst_num_existing_simplified:           0
% 2.33/0.98  inst_num_eq_res_simplified:             0
% 2.33/0.98  inst_num_child_elim:                    0
% 2.33/0.98  inst_num_of_dismatching_blockings:      13
% 2.33/0.98  inst_num_of_non_proper_insts:           147
% 2.33/0.98  inst_num_of_duplicates:                 0
% 2.33/0.98  inst_inst_num_from_inst_to_res:         0
% 2.33/0.98  inst_dismatching_checking_time:         0.
% 2.33/0.98  
% 2.33/0.98  ------ Resolution
% 2.33/0.98  
% 2.33/0.98  res_num_of_clauses:                     0
% 2.33/0.98  res_num_in_passive:                     0
% 2.33/0.98  res_num_in_active:                      0
% 2.33/0.98  res_num_of_loops:                       103
% 2.33/0.98  res_forward_subset_subsumed:            16
% 2.33/0.98  res_backward_subset_subsumed:           0
% 2.33/0.98  res_forward_subsumed:                   2
% 2.33/0.98  res_backward_subsumed:                  0
% 2.33/0.98  res_forward_subsumption_resolution:     1
% 2.33/0.98  res_backward_subsumption_resolution:    3
% 2.33/0.98  res_clause_to_clause_subsumption:       143
% 2.33/0.98  res_orphan_elimination:                 0
% 2.33/0.98  res_tautology_del:                      34
% 2.33/0.98  res_num_eq_res_simplified:              0
% 2.33/0.98  res_num_sel_changes:                    0
% 2.33/0.98  res_moves_from_active_to_pass:          0
% 2.33/0.98  
% 2.33/0.98  ------ Superposition
% 2.33/0.98  
% 2.33/0.98  sup_time_total:                         0.
% 2.33/0.98  sup_time_generating:                    0.
% 2.33/0.98  sup_time_sim_full:                      0.
% 2.33/0.98  sup_time_sim_immed:                     0.
% 2.33/0.98  
% 2.33/0.98  sup_num_of_clauses:                     38
% 2.33/0.98  sup_num_in_active:                      27
% 2.33/0.98  sup_num_in_passive:                     11
% 2.33/0.98  sup_num_of_loops:                       26
% 2.33/0.98  sup_fw_superposition:                   5
% 2.33/0.98  sup_bw_superposition:                   17
% 2.33/0.98  sup_immediate_simplified:               0
% 2.33/0.98  sup_given_eliminated:                   0
% 2.33/0.98  comparisons_done:                       0
% 2.33/0.98  comparisons_avoided:                    0
% 2.33/0.98  
% 2.33/0.98  ------ Simplifications
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  sim_fw_subset_subsumed:                 0
% 2.33/0.98  sim_bw_subset_subsumed:                 0
% 2.33/0.98  sim_fw_subsumed:                        0
% 2.33/0.98  sim_bw_subsumed:                        0
% 2.33/0.98  sim_fw_subsumption_res:                 0
% 2.33/0.98  sim_bw_subsumption_res:                 0
% 2.33/0.98  sim_tautology_del:                      2
% 2.33/0.98  sim_eq_tautology_del:                   0
% 2.33/0.98  sim_eq_res_simp:                        0
% 2.33/0.98  sim_fw_demodulated:                     0
% 2.33/0.98  sim_bw_demodulated:                     0
% 2.33/0.98  sim_light_normalised:                   0
% 2.33/0.98  sim_joinable_taut:                      0
% 2.33/0.98  sim_joinable_simp:                      0
% 2.33/0.98  sim_ac_normalised:                      0
% 2.33/0.98  sim_smt_subsumption:                    0
% 2.33/0.98  
%------------------------------------------------------------------------------
