%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:33 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  186 (4194 expanded)
%              Number of clauses        :  110 ( 900 expanded)
%              Number of leaves         :   22 ( 839 expanded)
%              Depth                    :   38
%              Number of atoms          :  741 (34732 expanded)
%              Number of equality atoms :  105 ( 767 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK6)
          | ~ v1_subset_1(sK6,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK6)
          | v1_subset_1(sK6,u1_struct_0(X0)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK5),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK5)) )
          & ( ~ r2_hidden(k3_yellow_0(sK5),X1)
            | v1_subset_1(X1,u1_struct_0(sK5)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
          & v13_waybel_0(X1,sK5)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK5)
      & v1_yellow_0(sK5)
      & v5_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( r2_hidden(k3_yellow_0(sK5),sK6)
      | ~ v1_subset_1(sK6,u1_struct_0(sK5)) )
    & ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
      | v1_subset_1(sK6,u1_struct_0(sK5)) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & v13_waybel_0(sK6,sK5)
    & ~ v1_xboole_0(sK6)
    & l1_orders_2(sK5)
    & v1_yellow_0(sK5)
    & v5_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f51,f50])).

fof(f86,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,X2,sK4(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK3(X0,X1),X3)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f85,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,negated_conjecture,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_264,plain,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | X1 = X0
    | u1_struct_0(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_264])).

cnf(c_478,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) = sK6 ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_480,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_27])).

cnf(c_15,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_582,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_583,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_1905,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_1908,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1911,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_16,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_453,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_454,plain,
    ( r1_orders_2(sK5,k3_yellow_0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_orders_2(sK5,k3_yellow_0(sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_33,c_32,c_30])).

cnf(c_459,plain,
    ( r1_orders_2(sK5,k3_yellow_0(sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_541,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ l1_orders_2(X1)
    | X4 != X3
    | k3_yellow_0(sK5) != X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_459])).

cnf(c_542,plain,
    ( ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK5),X0)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_69,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_546,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),X0)
    | r2_hidden(X1,X0)
    | ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_30,c_69])).

cnf(c_547,plain,
    ( ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK5),X0) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_1906,plain,
    ( v13_waybel_0(X0,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_2800,plain,
    ( v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1906])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,plain,
    ( v13_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2805,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2800,c_39])).

cnf(c_4215,plain,
    ( u1_struct_0(sK5) = sK6
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_2805])).

cnf(c_1262,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_1272,plain,
    ( k3_yellow_0(sK5) = k3_yellow_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1255,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1278,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_2408,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_1258,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2422,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X1 != u1_struct_0(sK5)
    | X0 != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_3860,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2422])).

cnf(c_3861,plain,
    ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5)
    | r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3860])).

cnf(c_1256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2331,plain,
    ( u1_struct_0(sK5) != X0
    | sK6 != X0
    | sK6 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_4531,plain,
    ( u1_struct_0(sK5) != sK6
    | sK6 = u1_struct_0(sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3117,plain,
    ( ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(k3_yellow_0(sK5),X0) ),
    inference(resolution,[status(thm)],[c_547,c_13])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4002,plain,
    ( ~ v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k3_yellow_0(sK5),X0)
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_3117,c_7])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2768,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(resolution,[status(thm)],[c_12,c_27])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2238,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2497,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_2781,plain,
    ( r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2768,c_29,c_27,c_2238,c_2497])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2818,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_2781,c_8])).

cnf(c_3491,plain,
    ( r2_hidden(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_2818])).

cnf(c_4292,plain,
    ( ~ v13_waybel_0(u1_struct_0(sK5),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_4002,c_3491])).

cnf(c_2807,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2805])).

cnf(c_4304,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | r2_hidden(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4292,c_2807,c_3491])).

cnf(c_4305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(renaming,[status(thm)],[c_4304])).

cnf(c_3206,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1260,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2321,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X1 != u1_struct_0(sK5)
    | X0 != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1260])).

cnf(c_2616,plain,
    ( m1_subset_1(k3_yellow_0(X0),X1)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X1 != u1_struct_0(sK5)
    | k3_yellow_0(X0) != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_3945,plain,
    ( m1_subset_1(k3_yellow_0(X0),sK6)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | k3_yellow_0(X0) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_3948,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | m1_subset_1(k3_yellow_0(sK5),sK6)
    | k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3945])).

cnf(c_4227,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6)
    | u1_struct_0(sK5) = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4215])).

cnf(c_4997,plain,
    ( r2_hidden(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_30,c_29,c_69,c_1272,c_1278,c_2408,c_3206,c_3491,c_3948,c_4227,c_4531])).

cnf(c_4998,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_4997])).

cnf(c_5016,plain,
    ( r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_4998,c_583])).

cnf(c_5017,plain,
    ( r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5016])).

cnf(c_5302,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_39,c_1272,c_1278,c_2408,c_2800,c_3861,c_4531,c_5017])).

cnf(c_5311,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_5302])).

cnf(c_5338,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5311])).

cnf(c_5987,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_5338])).

cnf(c_3121,plain,
    ( ~ v13_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(resolution,[status(thm)],[c_547,c_27])).

cnf(c_3124,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3121,c_2807])).

cnf(c_7053,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5987,c_3124])).

cnf(c_7064,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK5))
    | r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_7053,c_13])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7457,plain,
    ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6)
    | r1_tarski(u1_struct_0(sK5),X0) ),
    inference(resolution,[status(thm)],[c_7064,c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3774,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK5)),sK6)
    | r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_3491,c_0])).

cnf(c_8220,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(resolution,[status(thm)],[c_7457,c_3774])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6308,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),X0),X0)
    | ~ r2_hidden(sK1(u1_struct_0(sK5),X0),sK6)
    | X0 = u1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_3,c_3491])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6329,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
    | sK6 = u1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_6308,c_4])).

cnf(c_4504,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
    | sK6 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6662,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
    | sK6 = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6329,c_4504])).

cnf(c_6678,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
    | sK6 = u1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_6662,c_4])).

cnf(c_7473,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
    | sK6 = u1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_7064,c_6678])).

cnf(c_24,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_262,plain,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_262])).

cnf(c_492,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_7052,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sK6 != u1_struct_0(sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5987,c_492])).

cnf(c_2196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2562,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_5436,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_2905,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4319,plain,
    ( r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2905])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8220,c_7473,c_7052,c_6662,c_5436,c_4319])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.16/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.16/1.04  
% 1.16/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.16/1.04  
% 1.16/1.04  ------  iProver source info
% 1.16/1.04  
% 1.16/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.16/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.16/1.04  git: non_committed_changes: false
% 1.16/1.04  git: last_make_outside_of_git: false
% 1.16/1.04  
% 1.16/1.04  ------ 
% 1.16/1.04  ------ Parsing...
% 1.16/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.16/1.04  
% 1.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.16/1.04  
% 1.16/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.16/1.04  
% 1.16/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.16/1.04  ------ Proving...
% 1.16/1.04  ------ Problem Properties 
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  clauses                                 26
% 1.16/1.04  conjectures                             3
% 1.16/1.04  EPR                                     7
% 1.16/1.04  Horn                                    17
% 1.16/1.04  unary                                   4
% 1.16/1.04  binary                                  6
% 1.16/1.04  lits                                    69
% 1.16/1.04  lits eq                                 6
% 1.16/1.04  fd_pure                                 0
% 1.16/1.04  fd_pseudo                               0
% 1.16/1.04  fd_cond                                 0
% 1.16/1.04  fd_pseudo_cond                          4
% 1.16/1.04  AC symbols                              0
% 1.16/1.04  
% 1.16/1.04  ------ Input Options Time Limit: Unbounded
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  ------ 
% 1.16/1.04  Current options:
% 1.16/1.04  ------ 
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  ------ Proving...
% 1.16/1.04  
% 1.16/1.04  
% 1.16/1.04  % SZS status Theorem for theBenchmark.p
% 1.16/1.04  
% 1.16/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.16/1.04  
% 1.16/1.04  fof(f10,axiom,(
% 1.16/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f27,plain,(
% 1.16/1.04    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/1.04    inference(ennf_transformation,[],[f10])).
% 1.16/1.04  
% 1.16/1.04  fof(f47,plain,(
% 1.16/1.04    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/1.04    inference(nnf_transformation,[],[f27])).
% 1.16/1.04  
% 1.16/1.04  fof(f77,plain,(
% 1.16/1.04    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.16/1.04    inference(cnf_transformation,[],[f47])).
% 1.16/1.04  
% 1.16/1.04  fof(f11,conjecture,(
% 1.16/1.04    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f12,negated_conjecture,(
% 1.16/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.16/1.04    inference(negated_conjecture,[],[f11])).
% 1.16/1.04  
% 1.16/1.04  fof(f13,plain,(
% 1.16/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.16/1.04    inference(pure_predicate_removal,[],[f12])).
% 1.16/1.04  
% 1.16/1.04  fof(f14,plain,(
% 1.16/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.16/1.04    inference(pure_predicate_removal,[],[f13])).
% 1.16/1.04  
% 1.16/1.04  fof(f15,plain,(
% 1.16/1.04    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.16/1.04    inference(pure_predicate_removal,[],[f14])).
% 1.16/1.04  
% 1.16/1.04  fof(f28,plain,(
% 1.16/1.04    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.16/1.04    inference(ennf_transformation,[],[f15])).
% 1.16/1.04  
% 1.16/1.04  fof(f29,plain,(
% 1.16/1.04    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.16/1.04    inference(flattening,[],[f28])).
% 1.16/1.04  
% 1.16/1.04  fof(f48,plain,(
% 1.16/1.04    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.16/1.04    inference(nnf_transformation,[],[f29])).
% 1.16/1.04  
% 1.16/1.04  fof(f49,plain,(
% 1.16/1.04    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.16/1.04    inference(flattening,[],[f48])).
% 1.16/1.04  
% 1.16/1.04  fof(f51,plain,(
% 1.16/1.04    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK6) | ~v1_subset_1(sK6,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK6) | v1_subset_1(sK6,u1_struct_0(X0))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK6,X0) & ~v1_xboole_0(sK6))) )),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f50,plain,(
% 1.16/1.04    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK5),X1) | ~v1_subset_1(X1,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),X1) | v1_subset_1(X1,u1_struct_0(sK5))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(X1,sK5) & ~v1_xboole_0(X1)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5))),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f52,plain,(
% 1.16/1.04    ((r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(sK6,sK5) & ~v1_xboole_0(sK6)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5)),
% 1.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f49,f51,f50])).
% 1.16/1.04  
% 1.16/1.04  fof(f86,plain,(
% 1.16/1.04    r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f84,plain,(
% 1.16/1.04    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f7,axiom,(
% 1.16/1.04    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f22,plain,(
% 1.16/1.04    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(ennf_transformation,[],[f7])).
% 1.16/1.04  
% 1.16/1.04  fof(f68,plain,(
% 1.16/1.04    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f22])).
% 1.16/1.04  
% 1.16/1.04  fof(f81,plain,(
% 1.16/1.04    l1_orders_2(sK5)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f9,axiom,(
% 1.16/1.04    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f25,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(ennf_transformation,[],[f9])).
% 1.16/1.04  
% 1.16/1.04  fof(f26,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(flattening,[],[f25])).
% 1.16/1.04  
% 1.16/1.04  fof(f42,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(nnf_transformation,[],[f26])).
% 1.16/1.04  
% 1.16/1.04  fof(f43,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(rectify,[],[f42])).
% 1.16/1.04  
% 1.16/1.04  fof(f45,plain,(
% 1.16/1.04    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,X2,sK4(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))) )),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f44,plain,(
% 1.16/1.04    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK3(X0,X1),X3) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f46,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f45,f44])).
% 1.16/1.04  
% 1.16/1.04  fof(f70,plain,(
% 1.16/1.04    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f46])).
% 1.16/1.04  
% 1.16/1.04  fof(f8,axiom,(
% 1.16/1.04    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f23,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.16/1.04    inference(ennf_transformation,[],[f8])).
% 1.16/1.04  
% 1.16/1.04  fof(f24,plain,(
% 1.16/1.04    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.16/1.04    inference(flattening,[],[f23])).
% 1.16/1.04  
% 1.16/1.04  fof(f69,plain,(
% 1.16/1.04    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f24])).
% 1.16/1.04  
% 1.16/1.04  fof(f80,plain,(
% 1.16/1.04    v1_yellow_0(sK5)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f78,plain,(
% 1.16/1.04    ~v2_struct_0(sK5)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f79,plain,(
% 1.16/1.04    v5_orders_2(sK5)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f83,plain,(
% 1.16/1.04    v13_waybel_0(sK6,sK5)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f5,axiom,(
% 1.16/1.04    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f19,plain,(
% 1.16/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.16/1.04    inference(ennf_transformation,[],[f5])).
% 1.16/1.04  
% 1.16/1.04  fof(f66,plain,(
% 1.16/1.04    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f19])).
% 1.16/1.04  
% 1.16/1.04  fof(f3,axiom,(
% 1.16/1.04    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f37,plain,(
% 1.16/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/1.04    inference(nnf_transformation,[],[f3])).
% 1.16/1.04  
% 1.16/1.04  fof(f38,plain,(
% 1.16/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/1.04    inference(rectify,[],[f37])).
% 1.16/1.04  
% 1.16/1.04  fof(f39,plain,(
% 1.16/1.04    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f40,plain,(
% 1.16/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.16/1.04  
% 1.16/1.04  fof(f59,plain,(
% 1.16/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.16/1.04    inference(cnf_transformation,[],[f40])).
% 1.16/1.04  
% 1.16/1.04  fof(f87,plain,(
% 1.16/1.04    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.16/1.04    inference(equality_resolution,[],[f59])).
% 1.16/1.04  
% 1.16/1.04  fof(f1,axiom,(
% 1.16/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f16,plain,(
% 1.16/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.16/1.04    inference(ennf_transformation,[],[f1])).
% 1.16/1.04  
% 1.16/1.04  fof(f30,plain,(
% 1.16/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.16/1.04    inference(nnf_transformation,[],[f16])).
% 1.16/1.04  
% 1.16/1.04  fof(f31,plain,(
% 1.16/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.16/1.04    inference(rectify,[],[f30])).
% 1.16/1.04  
% 1.16/1.04  fof(f32,plain,(
% 1.16/1.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f33,plain,(
% 1.16/1.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.16/1.04  
% 1.16/1.04  fof(f53,plain,(
% 1.16/1.04    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f33])).
% 1.16/1.04  
% 1.16/1.04  fof(f4,axiom,(
% 1.16/1.04    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f18,plain,(
% 1.16/1.04    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.16/1.04    inference(ennf_transformation,[],[f4])).
% 1.16/1.04  
% 1.16/1.04  fof(f41,plain,(
% 1.16/1.04    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.16/1.04    inference(nnf_transformation,[],[f18])).
% 1.16/1.04  
% 1.16/1.04  fof(f62,plain,(
% 1.16/1.04    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f41])).
% 1.16/1.04  
% 1.16/1.04  fof(f82,plain,(
% 1.16/1.04    ~v1_xboole_0(sK6)),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  fof(f64,plain,(
% 1.16/1.04    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f41])).
% 1.16/1.04  
% 1.16/1.04  fof(f58,plain,(
% 1.16/1.04    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.16/1.04    inference(cnf_transformation,[],[f40])).
% 1.16/1.04  
% 1.16/1.04  fof(f88,plain,(
% 1.16/1.04    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.16/1.04    inference(equality_resolution,[],[f58])).
% 1.16/1.04  
% 1.16/1.04  fof(f54,plain,(
% 1.16/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f33])).
% 1.16/1.04  
% 1.16/1.04  fof(f55,plain,(
% 1.16/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f33])).
% 1.16/1.04  
% 1.16/1.04  fof(f2,axiom,(
% 1.16/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.16/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.16/1.04  
% 1.16/1.04  fof(f17,plain,(
% 1.16/1.04    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.16/1.04    inference(ennf_transformation,[],[f2])).
% 1.16/1.04  
% 1.16/1.04  fof(f34,plain,(
% 1.16/1.04    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.16/1.04    inference(nnf_transformation,[],[f17])).
% 1.16/1.04  
% 1.16/1.04  fof(f35,plain,(
% 1.16/1.04    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 1.16/1.04    introduced(choice_axiom,[])).
% 1.16/1.04  
% 1.16/1.04  fof(f36,plain,(
% 1.16/1.04    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 1.16/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 1.16/1.04  
% 1.16/1.04  fof(f57,plain,(
% 1.16/1.04    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f36])).
% 1.16/1.04  
% 1.16/1.04  fof(f56,plain,(
% 1.16/1.04    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.16/1.04    inference(cnf_transformation,[],[f36])).
% 1.16/1.04  
% 1.16/1.04  fof(f76,plain,(
% 1.16/1.04    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.16/1.04    inference(cnf_transformation,[],[f47])).
% 1.16/1.04  
% 1.16/1.04  fof(f89,plain,(
% 1.16/1.04    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.16/1.04    inference(equality_resolution,[],[f76])).
% 1.16/1.04  
% 1.16/1.04  fof(f85,plain,(
% 1.16/1.04    ~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))),
% 1.16/1.04    inference(cnf_transformation,[],[f52])).
% 1.16/1.04  
% 1.16/1.04  cnf(c_23,plain,
% 1.16/1.04      ( v1_subset_1(X0,X1)
% 1.16/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.16/1.04      | X0 = X1 ),
% 1.16/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_25,negated_conjecture,
% 1.16/1.04      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(cnf_transformation,[],[f86]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_264,plain,
% 1.16/1.04      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(prop_impl,[status(thm)],[c_25]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_477,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | X1 = X0
% 1.16/1.04      | u1_struct_0(sK5) != X1
% 1.16/1.04      | sK6 != X0 ),
% 1.16/1.04      inference(resolution_lifted,[status(thm)],[c_23,c_264]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_478,plain,
% 1.16/1.04      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | u1_struct_0(sK5) = sK6 ),
% 1.16/1.04      inference(unflattening,[status(thm)],[c_477]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_27,negated_conjecture,
% 1.16/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(cnf_transformation,[],[f84]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_480,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),sK6) | u1_struct_0(sK5) = sK6 ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_478,c_27]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_15,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 1.16/1.04      | ~ l1_orders_2(X0) ),
% 1.16/1.04      inference(cnf_transformation,[],[f68]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_30,negated_conjecture,
% 1.16/1.04      ( l1_orders_2(sK5) ),
% 1.16/1.04      inference(cnf_transformation,[],[f81]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_582,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK5 != X0 ),
% 1.16/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_583,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
% 1.16/1.04      inference(unflattening,[status(thm)],[c_582]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1905,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1908,plain,
% 1.16/1.04      ( u1_struct_0(sK5) = sK6
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1911,plain,
% 1.16/1.04      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_22,plain,
% 1.16/1.04      ( ~ r1_orders_2(X0,X1,X2)
% 1.16/1.04      | ~ v13_waybel_0(X3,X0)
% 1.16/1.04      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.16/1.04      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.16/1.04      | ~ r2_hidden(X1,X3)
% 1.16/1.04      | r2_hidden(X2,X3)
% 1.16/1.04      | ~ l1_orders_2(X0) ),
% 1.16/1.04      inference(cnf_transformation,[],[f70]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_16,plain,
% 1.16/1.04      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.16/1.04      | v2_struct_0(X0)
% 1.16/1.04      | ~ v5_orders_2(X0)
% 1.16/1.04      | ~ v1_yellow_0(X0)
% 1.16/1.04      | ~ l1_orders_2(X0) ),
% 1.16/1.04      inference(cnf_transformation,[],[f69]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_31,negated_conjecture,
% 1.16/1.04      ( v1_yellow_0(sK5) ),
% 1.16/1.04      inference(cnf_transformation,[],[f80]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_453,plain,
% 1.16/1.04      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.16/1.04      | v2_struct_0(X0)
% 1.16/1.04      | ~ v5_orders_2(X0)
% 1.16/1.04      | ~ l1_orders_2(X0)
% 1.16/1.04      | sK5 != X0 ),
% 1.16/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_454,plain,
% 1.16/1.04      ( r1_orders_2(sK5,k3_yellow_0(sK5),X0)
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | v2_struct_0(sK5)
% 1.16/1.04      | ~ v5_orders_2(sK5)
% 1.16/1.04      | ~ l1_orders_2(sK5) ),
% 1.16/1.04      inference(unflattening,[status(thm)],[c_453]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_33,negated_conjecture,
% 1.16/1.04      ( ~ v2_struct_0(sK5) ),
% 1.16/1.04      inference(cnf_transformation,[],[f78]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_32,negated_conjecture,
% 1.16/1.04      ( v5_orders_2(sK5) ),
% 1.16/1.04      inference(cnf_transformation,[],[f79]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_458,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r1_orders_2(sK5,k3_yellow_0(sK5),X0) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_454,c_33,c_32,c_30]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_459,plain,
% 1.16/1.04      ( r1_orders_2(sK5,k3_yellow_0(sK5),X0)
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(renaming,[status(thm)],[c_458]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_541,plain,
% 1.16/1.04      ( ~ v13_waybel_0(X0,X1)
% 1.16/1.04      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.16/1.04      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.16/1.04      | ~ m1_subset_1(X4,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.16/1.04      | ~ r2_hidden(X2,X0)
% 1.16/1.04      | r2_hidden(X3,X0)
% 1.16/1.04      | ~ l1_orders_2(X1)
% 1.16/1.04      | X4 != X3
% 1.16/1.04      | k3_yellow_0(sK5) != X2
% 1.16/1.04      | sK5 != X1 ),
% 1.16/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_459]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_542,plain,
% 1.16/1.04      ( ~ v13_waybel_0(X0,sK5)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X1,X0)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),X0)
% 1.16/1.04      | ~ l1_orders_2(sK5) ),
% 1.16/1.04      inference(unflattening,[status(thm)],[c_541]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_69,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | ~ l1_orders_2(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_15]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_546,plain,
% 1.16/1.04      ( ~ r2_hidden(k3_yellow_0(sK5),X0)
% 1.16/1.04      | r2_hidden(X1,X0)
% 1.16/1.04      | ~ v13_waybel_0(X0,sK5)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_542,c_30,c_69]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_547,plain,
% 1.16/1.04      ( ~ v13_waybel_0(X0,sK5)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | r2_hidden(X1,X0)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),X0) ),
% 1.16/1.04      inference(renaming,[status(thm)],[c_546]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1906,plain,
% 1.16/1.04      ( v13_waybel_0(X0,sK5) != iProver_top
% 1.16/1.04      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 1.16/1.04      | r2_hidden(X1,X0) = iProver_top
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),X0) != iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2800,plain,
% 1.16/1.04      ( v13_waybel_0(sK6,sK5) != iProver_top
% 1.16/1.04      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | r2_hidden(X0,sK6) = iProver_top
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 1.16/1.04      inference(superposition,[status(thm)],[c_1911,c_1906]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_28,negated_conjecture,
% 1.16/1.04      ( v13_waybel_0(sK6,sK5) ),
% 1.16/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_39,plain,
% 1.16/1.04      ( v13_waybel_0(sK6,sK5) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2805,plain,
% 1.16/1.04      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | r2_hidden(X0,sK6) = iProver_top
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_2800,c_39]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4215,plain,
% 1.16/1.04      ( u1_struct_0(sK5) = sK6
% 1.16/1.04      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | r2_hidden(X0,sK6) = iProver_top ),
% 1.16/1.04      inference(superposition,[status(thm)],[c_1908,c_2805]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1262,plain,
% 1.16/1.04      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 1.16/1.04      theory(equality) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1272,plain,
% 1.16/1.04      ( k3_yellow_0(sK5) = k3_yellow_0(sK5) | sK5 != sK5 ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1262]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1255,plain,( X0 = X0 ),theory(equality) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1278,plain,
% 1.16/1.04      ( sK5 = sK5 ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1255]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2408,plain,
% 1.16/1.04      ( sK6 = sK6 ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1255]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1258,plain,
% 1.16/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.16/1.04      theory(equality) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2422,plain,
% 1.16/1.04      ( r2_hidden(X0,X1)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | X1 != u1_struct_0(sK5)
% 1.16/1.04      | X0 != k3_yellow_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1258]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3860,plain,
% 1.16/1.04      ( ~ r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 1.16/1.04      | sK6 != u1_struct_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_2422]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3861,plain,
% 1.16/1.04      ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 1.16/1.04      | sK6 != u1_struct_0(sK5)
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_3860]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1256,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2331,plain,
% 1.16/1.04      ( u1_struct_0(sK5) != X0 | sK6 != X0 | sK6 = u1_struct_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1256]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4531,plain,
% 1.16/1.04      ( u1_struct_0(sK5) != sK6 | sK6 = u1_struct_0(sK5) | sK6 != sK6 ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_2331]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_13,plain,
% 1.16/1.04      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f66]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3117,plain,
% 1.16/1.04      ( ~ v13_waybel_0(X0,sK5)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X1,X0)
% 1.16/1.04      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),X0) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_547,c_13]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_7,plain,
% 1.16/1.04      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f87]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4002,plain,
% 1.16/1.04      ( ~ v13_waybel_0(X0,sK5)
% 1.16/1.04      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X1,X0)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),X0)
% 1.16/1.04      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_3117,c_7]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2,plain,
% 1.16/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.16/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_12,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2768,plain,
% 1.16/1.04      ( r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_12,c_27]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_29,negated_conjecture,
% 1.16/1.04      ( ~ v1_xboole_0(sK6) ),
% 1.16/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2238,plain,
% 1.16/1.04      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_10,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.16/1.04      inference(cnf_transformation,[],[f64]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2333,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | v1_xboole_0(X0)
% 1.16/1.04      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2497,plain,
% 1.16/1.04      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.04      | v1_xboole_0(sK6) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_2333]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2781,plain,
% 1.16/1.04      ( r2_hidden(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_2768,c_29,c_27,c_2238,c_2497]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_8,plain,
% 1.16/1.04      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f88]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2818,plain,
% 1.16/1.04      ( r1_tarski(sK6,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_2781,c_8]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3491,plain,
% 1.16/1.04      ( r2_hidden(X0,u1_struct_0(sK5)) | ~ r2_hidden(X0,sK6) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_2,c_2818]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4292,plain,
% 1.16/1.04      ( ~ v13_waybel_0(u1_struct_0(sK5),sK5)
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,u1_struct_0(sK5))
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_4002,c_3491]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2807,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,sK6)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2805]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4304,plain,
% 1.16/1.04      ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | r2_hidden(X0,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_4292,c_2807,c_3491]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4305,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,u1_struct_0(sK5))
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(renaming,[status(thm)],[c_4304]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3206,plain,
% 1.16/1.04      ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | v1_xboole_0(sK6) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1260,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.16/1.04      theory(equality) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2321,plain,
% 1.16/1.04      ( m1_subset_1(X0,X1)
% 1.16/1.04      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | X1 != u1_struct_0(sK5)
% 1.16/1.04      | X0 != k3_yellow_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_1260]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_2616,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(X0),X1)
% 1.16/1.04      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | X1 != u1_struct_0(sK5)
% 1.16/1.04      | k3_yellow_0(X0) != k3_yellow_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_2321]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3945,plain,
% 1.16/1.04      ( m1_subset_1(k3_yellow_0(X0),sK6)
% 1.16/1.04      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | k3_yellow_0(X0) != k3_yellow_0(sK5)
% 1.16/1.04      | sK6 != u1_struct_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_2616]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3948,plain,
% 1.16/1.04      ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 1.16/1.04      | m1_subset_1(k3_yellow_0(sK5),sK6)
% 1.16/1.04      | k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 1.16/1.04      | sK6 != u1_struct_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_3945]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4227,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,sK6)
% 1.16/1.04      | u1_struct_0(sK5) = sK6 ),
% 1.16/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_4215]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4997,plain,
% 1.16/1.04      ( r2_hidden(X0,u1_struct_0(sK5))
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_4305,c_30,c_29,c_69,c_1272,c_1278,c_2408,c_3206,
% 1.16/1.04                 c_3491,c_3948,c_4227,c_4531]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4998,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(renaming,[status(thm)],[c_4997]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5016,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_4998,c_583]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5017,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 1.16/1.04      inference(predicate_to_equality,[status(thm)],[c_5016]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5302,plain,
% 1.16/1.04      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 1.16/1.04      | r2_hidden(X0,sK6) = iProver_top ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_4215,c_39,c_1272,c_1278,c_2408,c_2800,c_3861,c_4531,
% 1.16/1.04                 c_5017]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5311,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 1.16/1.04      inference(superposition,[status(thm)],[c_1905,c_5302]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5338,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_5311]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_5987,plain,
% 1.16/1.04      ( r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_480,c_5338]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3121,plain,
% 1.16/1.04      ( ~ v13_waybel_0(sK6,sK5)
% 1.16/1.04      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,sK6)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_547,c_27]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3124,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 1.16/1.04      | r2_hidden(X0,sK6)
% 1.16/1.04      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_3121,c_2807]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_7053,plain,
% 1.16/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK5)) | r2_hidden(X0,sK6) ),
% 1.16/1.04      inference(backward_subsumption_resolution,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_5987,c_3124]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_7064,plain,
% 1.16/1.04      ( ~ r2_hidden(X0,u1_struct_0(sK5)) | r2_hidden(X0,sK6) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_7053,c_13]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_1,plain,
% 1.16/1.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_7457,plain,
% 1.16/1.04      ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6)
% 1.16/1.04      | r1_tarski(u1_struct_0(sK5),X0) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_7064,c_1]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_0,plain,
% 1.16/1.04      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.16/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3774,plain,
% 1.16/1.04      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK5)),sK6)
% 1.16/1.04      | r1_tarski(X0,u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_3491,c_0]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_8220,plain,
% 1.16/1.04      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_7457,c_3774]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_3,plain,
% 1.16/1.04      ( ~ r2_hidden(sK1(X0,X1),X1)
% 1.16/1.04      | ~ r2_hidden(sK1(X0,X1),X0)
% 1.16/1.04      | X1 = X0 ),
% 1.16/1.04      inference(cnf_transformation,[],[f57]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_6308,plain,
% 1.16/1.04      ( ~ r2_hidden(sK1(u1_struct_0(sK5),X0),X0)
% 1.16/1.04      | ~ r2_hidden(sK1(u1_struct_0(sK5),X0),sK6)
% 1.16/1.04      | X0 = u1_struct_0(sK5) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_3,c_3491]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4,plain,
% 1.16/1.04      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 1.16/1.04      inference(cnf_transformation,[],[f56]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_6329,plain,
% 1.16/1.04      ( r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 1.16/1.04      | ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
% 1.16/1.04      | sK6 = u1_struct_0(sK5) ),
% 1.16/1.04      inference(resolution,[status(thm)],[c_6308,c_4]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_4504,plain,
% 1.16/1.04      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 1.16/1.04      | ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
% 1.16/1.04      | sK6 = u1_struct_0(sK5) ),
% 1.16/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_6662,plain,
% 1.16/1.04      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
% 1.16/1.04      | sK6 = u1_struct_0(sK5) ),
% 1.16/1.04      inference(global_propositional_subsumption,
% 1.16/1.04                [status(thm)],
% 1.16/1.04                [c_6329,c_4504]) ).
% 1.16/1.04  
% 1.16/1.04  cnf(c_6678,plain,
% 1.16/1.04      ( r2_hidden(sK1(u1_struct_0(sK5),sK6),u1_struct_0(sK5))
% 1.16/1.05      | sK6 = u1_struct_0(sK5) ),
% 1.16/1.05      inference(resolution,[status(thm)],[c_6662,c_4]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_7473,plain,
% 1.16/1.05      ( r2_hidden(sK1(u1_struct_0(sK5),sK6),sK6)
% 1.16/1.05      | sK6 = u1_struct_0(sK5) ),
% 1.16/1.05      inference(resolution,[status(thm)],[c_7064,c_6678]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_24,plain,
% 1.16/1.05      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 1.16/1.05      inference(cnf_transformation,[],[f89]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_26,negated_conjecture,
% 1.16/1.05      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 1.16/1.05      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.05      inference(cnf_transformation,[],[f85]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_262,plain,
% 1.16/1.05      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 1.16/1.05      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 1.16/1.05      inference(prop_impl,[status(thm)],[c_26]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_491,plain,
% 1.16/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 1.16/1.05      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.05      | u1_struct_0(sK5) != X0
% 1.16/1.05      | sK6 != X0 ),
% 1.16/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_262]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_492,plain,
% 1.16/1.05      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 1.16/1.05      | sK6 != u1_struct_0(sK5) ),
% 1.16/1.05      inference(unflattening,[status(thm)],[c_491]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_7052,plain,
% 1.16/1.05      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | sK6 != u1_struct_0(sK5) ),
% 1.16/1.05      inference(backward_subsumption_resolution,
% 1.16/1.05                [status(thm)],
% 1.16/1.05                [c_5987,c_492]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_2196,plain,
% 1.16/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.16/1.05      | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.16/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_2562,plain,
% 1.16/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.05      inference(instantiation,[status(thm)],[c_2196]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_5436,plain,
% 1.16/1.05      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 1.16/1.05      inference(instantiation,[status(thm)],[c_2562]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_2905,plain,
% 1.16/1.05      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 1.16/1.05      inference(instantiation,[status(thm)],[c_7]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(c_4319,plain,
% 1.16/1.05      ( r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 1.16/1.05      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 1.16/1.05      inference(instantiation,[status(thm)],[c_2905]) ).
% 1.16/1.05  
% 1.16/1.05  cnf(contradiction,plain,
% 1.16/1.05      ( $false ),
% 1.16/1.05      inference(minisat,
% 1.16/1.05                [status(thm)],
% 1.16/1.05                [c_8220,c_7473,c_7052,c_6662,c_5436,c_4319]) ).
% 1.16/1.05  
% 1.16/1.05  
% 1.16/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.16/1.05  
% 1.16/1.05  ------                               Statistics
% 1.16/1.05  
% 1.16/1.05  ------ Selected
% 1.16/1.05  
% 1.16/1.05  total_time:                             0.283
% 1.16/1.05  
%------------------------------------------------------------------------------
