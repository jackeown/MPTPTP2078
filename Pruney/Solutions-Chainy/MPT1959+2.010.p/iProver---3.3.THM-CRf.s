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
% DateTime   : Thu Dec  3 12:28:25 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  251 (2146 expanded)
%              Number of clauses        :  159 ( 507 expanded)
%              Number of leaves         :   24 ( 408 expanded)
%              Depth                    :   32
%              Number of atoms          : 1036 (16900 expanded)
%              Number of equality atoms :  228 ( 504 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,X2,sK3(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK5)
          | ~ v1_subset_1(sK5,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK5)
          | v1_subset_1(sK5,u1_struct_0(X0)) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK4),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK4)) )
          & ( ~ r2_hidden(k3_yellow_0(sK4),X1)
            | v1_subset_1(X1,u1_struct_0(sK4)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v13_waybel_0(X1,sK4)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK4)
      & v1_yellow_0(sK4)
      & v5_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( r2_hidden(k3_yellow_0(sK4),sK5)
      | ~ v1_subset_1(sK5,u1_struct_0(sK4)) )
    & ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
      | v1_subset_1(sK5,u1_struct_0(sK4)) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v13_waybel_0(sK5,sK4)
    & ~ v1_xboole_0(sK5)
    & l1_orders_2(sK4)
    & v1_yellow_0(sK4)
    & v5_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).

fof(f94,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f62])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
          | ~ r2_hidden(sK0(X0,X1,X2),X1) )
        & ( r2_hidden(sK0(X0,X1,X2),X2)
          | r2_hidden(sK0(X0,X1,X2),X1) )
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK0(X0,X1,X2),X2)
              | ~ r2_hidden(sK0(X0,X1,X2),X1) )
            & ( r2_hidden(sK0(X0,X1,X2),X2)
              | r2_hidden(sK0(X0,X1,X2),X1) )
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f98,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_692,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_693,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ v13_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_709,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ v13_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_693,c_10])).

cnf(c_12440,plain,
    ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,u1_struct_0(sK4))
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_21403,plain,
    ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
    | ~ v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12440])).

cnf(c_5870,plain,
    ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_11153,plain,
    ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
    | ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),sK5)
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
    inference(instantiation,[status(thm)],[c_5870])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_293,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_366,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_293])).

cnf(c_5860,plain,
    ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_10178,plain,
    ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4))
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5860])).

cnf(c_2234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_773,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_774,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_2221,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_19,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_732,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_733,plain,
    ( r2_lattice3(sK4,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_17,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_17])).

cnf(c_227,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_18,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_517,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_518,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_72,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_520,plain,
    ( r1_yellow_0(sK4,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_36,c_35,c_34,c_33,c_72])).

cnf(c_567,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_520])).

cnf(c_568,plain,
    ( ~ r2_lattice3(sK4,k1_xboole_0,X0)
    | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ r2_lattice3(sK4,k1_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_33])).

cnf(c_573,plain,
    ( ~ r2_lattice3(sK4,k1_xboole_0,X0)
    | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_830,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_733,c_573])).

cnf(c_2218,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_753,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_754,plain,
    ( k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_2259,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2218,c_754])).

cnf(c_2225,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_4053,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | r1_tarski(X2,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_2225])).

cnf(c_5405,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_4053])).

cnf(c_5445,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X1),X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2221,c_5405])).

cnf(c_6610,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) = iProver_top
    | r2_hidden(sK3(sK4,X1),X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_5445])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2235,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2231,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2232,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3716,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_2232])).

cnf(c_5441,plain,
    ( v13_waybel_0(X0,sK4) != iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_5405])).

cnf(c_5717,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2235,c_5441])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2939,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_30])).

cnf(c_3453,plain,
    ( r2_hidden(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_366,c_2939])).

cnf(c_3454,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3453])).

cnf(c_6094,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5717,c_3454])).

cnf(c_6095,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6094])).

cnf(c_20,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_803,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_804,plain,
    ( v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK3(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_2219,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK3(sK4,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2922,plain,
    ( v13_waybel_0(X0,sK4) = iProver_top
    | r2_hidden(sK3(sK4,X0),X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_2219])).

cnf(c_6103,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6095,c_2922])).

cnf(c_3582,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) ),
    inference(resolution,[status(thm)],[c_804,c_3453])).

cnf(c_2483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2648,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_2649,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3922,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3582,c_2648,c_2649])).

cnf(c_3924,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3922])).

cnf(c_6921,plain,
    ( r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top
    | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6103,c_3924])).

cnf(c_6922,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6921])).

cnf(c_7663,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6610,c_6922])).

cnf(c_7723,plain,
    ( v13_waybel_0(u1_struct_0(sK4),sK4)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7663])).

cnf(c_744,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_745,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_2223,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_2495,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_754,c_2223])).

cnf(c_26,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_372,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_26,c_293])).

cnf(c_28,negated_conjecture,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_296,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_533,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_372,c_296])).

cnf(c_534,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_2227,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_535,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2488,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2489,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2488])).

cnf(c_6268,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_43,c_535,c_2489])).

cnf(c_6269,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_6268])).

cnf(c_4054,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_2225])).

cnf(c_31,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_954,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_709])).

cnf(c_955,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_957,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r1_orders_2(sK4,X0,X1)
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_30])).

cnf(c_958,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(renaming,[status(thm)],[c_957])).

cnf(c_959,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_4098,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4054,c_959])).

cnf(c_4107,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2259,c_4098])).

cnf(c_6276,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6269,c_4107])).

cnf(c_93,plain,
    ( ~ l1_orders_2(sK4)
    | k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3103,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(resolution,[status(thm)],[c_709,c_30])).

cnf(c_3208,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3103,c_30,c_955])).

cnf(c_3232,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
    inference(resolution,[status(thm)],[c_3208,c_830])).

cnf(c_3233,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3232])).

cnf(c_1591,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3266,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | X1 != u1_struct_0(sK4)
    | X0 != k3_yellow_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_3642,plain,
    ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),X0)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | X0 != u1_struct_0(sK4)
    | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3266])).

cnf(c_4734,plain,
    ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
    | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3642])).

cnf(c_4736,plain,
    ( k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
    | sK5 != u1_struct_0(sK4)
    | m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5) = iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4734])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_4735,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5)
    | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_4738,plain,
    ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4735])).

cnf(c_1587,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1586,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4846,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1587,c_1586])).

cnf(c_2948,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2939,c_534])).

cnf(c_6703,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | sK5 = u1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_4846,c_2948])).

cnf(c_6704,plain,
    ( sK5 = u1_struct_0(sK4)
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6703])).

cnf(c_7355,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6276,c_33,c_93,c_2495,c_3233,c_4107,c_4736,c_4738,c_6704])).

cnf(c_7369,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2495,c_7355])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | ~ r2_hidden(sK0(X1,X0,X2),X0)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X2,X0),X0)
    | ~ r2_hidden(sK0(X1,X2,X0),X2)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_293])).

cnf(c_1196,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_1197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1196])).

cnf(c_1249,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_367,c_1197])).

cnf(c_5329,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),sK5)
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_5324,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1589,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2687,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | X0 != k3_yellow_0(sK4)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_3152,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | X0 != k3_yellow_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_5128,plain,
    ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3152])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X2,X0),X1)
    | ~ r1_tarski(X2,X1)
    | X0 = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_293])).

cnf(c_1251,plain,
    ( m1_subset_1(sK0(X0,X1,X2),X0)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X1,X0)
    | X2 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_369,c_1197])).

cnf(c_2574,plain,
    ( m1_subset_1(sK0(X0,u1_struct_0(sK4),sK5),X0)
    | ~ r1_tarski(u1_struct_0(sK4),X0)
    | ~ r1_tarski(sK5,X0)
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_3135,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2574])).

cnf(c_2652,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_2650,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2648])).

cnf(c_2635,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_27,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_29,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_294,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_294])).

cnf(c_547,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK5 != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_548,plain,
    ( sK5 != u1_struct_0(sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21403,c_11153,c_10178,c_7723,c_7369,c_6703,c_5329,c_5324,c_5128,c_3135,c_2652,c_2649,c_2650,c_2648,c_2635,c_2488,c_548,c_93,c_30,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:13:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 7.12/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.48  
% 7.12/1.48  ------  iProver source info
% 7.12/1.48  
% 7.12/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.48  git: non_committed_changes: false
% 7.12/1.48  git: last_make_outside_of_git: false
% 7.12/1.48  
% 7.12/1.48  ------ 
% 7.12/1.48  ------ Parsing...
% 7.12/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.48  
% 7.12/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.48  ------ Proving...
% 7.12/1.48  ------ Problem Properties 
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  clauses                                 25
% 7.12/1.48  conjectures                             2
% 7.12/1.48  EPR                                     5
% 7.12/1.48  Horn                                    17
% 7.12/1.48  unary                                   5
% 7.12/1.48  binary                                  4
% 7.12/1.48  lits                                    69
% 7.12/1.48  lits eq                                 9
% 7.12/1.48  fd_pure                                 0
% 7.12/1.48  fd_pseudo                               0
% 7.12/1.48  fd_cond                                 2
% 7.12/1.48  fd_pseudo_cond                          4
% 7.12/1.48  AC symbols                              0
% 7.12/1.48  
% 7.12/1.48  ------ Input Options Time Limit: Unbounded
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  ------ 
% 7.12/1.48  Current options:
% 7.12/1.48  ------ 
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  ------ Proving...
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  % SZS status Theorem for theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  fof(f12,axiom,(
% 7.12/1.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f35,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(ennf_transformation,[],[f12])).
% 7.12/1.48  
% 7.12/1.48  fof(f36,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(flattening,[],[f35])).
% 7.12/1.48  
% 7.12/1.48  fof(f52,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(nnf_transformation,[],[f36])).
% 7.12/1.48  
% 7.12/1.48  fof(f53,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(rectify,[],[f52])).
% 7.12/1.48  
% 7.12/1.48  fof(f55,plain,(
% 7.12/1.48    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f54,plain,(
% 7.12/1.48    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f56,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).
% 7.12/1.48  
% 7.12/1.48  fof(f83,plain,(
% 7.12/1.48    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f56])).
% 7.12/1.48  
% 7.12/1.48  fof(f14,conjecture,(
% 7.12/1.48    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f15,negated_conjecture,(
% 7.12/1.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.12/1.48    inference(negated_conjecture,[],[f14])).
% 7.12/1.48  
% 7.12/1.48  fof(f16,plain,(
% 7.12/1.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f15])).
% 7.12/1.48  
% 7.12/1.48  fof(f17,plain,(
% 7.12/1.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f16])).
% 7.12/1.48  
% 7.12/1.48  fof(f18,plain,(
% 7.12/1.48    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f17])).
% 7.12/1.48  
% 7.12/1.48  fof(f38,plain,(
% 7.12/1.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.12/1.48    inference(ennf_transformation,[],[f18])).
% 7.12/1.48  
% 7.12/1.48  fof(f39,plain,(
% 7.12/1.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.12/1.48    inference(flattening,[],[f38])).
% 7.12/1.48  
% 7.12/1.48  fof(f58,plain,(
% 7.12/1.48    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.12/1.48    inference(nnf_transformation,[],[f39])).
% 7.12/1.48  
% 7.12/1.48  fof(f59,plain,(
% 7.12/1.48    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.12/1.48    inference(flattening,[],[f58])).
% 7.12/1.48  
% 7.12/1.48  fof(f61,plain,(
% 7.12/1.48    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f60,plain,(
% 7.12/1.48    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f62,plain,(
% 7.12/1.48    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & ~v2_struct_0(sK4)),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f59,f61,f60])).
% 7.12/1.48  
% 7.12/1.48  fof(f94,plain,(
% 7.12/1.48    l1_orders_2(sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f6,axiom,(
% 7.12/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f26,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.12/1.48    inference(ennf_transformation,[],[f6])).
% 7.12/1.48  
% 7.12/1.48  fof(f27,plain,(
% 7.12/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.12/1.48    inference(flattening,[],[f26])).
% 7.12/1.48  
% 7.12/1.48  fof(f73,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f27])).
% 7.12/1.48  
% 7.12/1.48  fof(f2,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f21,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(ennf_transformation,[],[f2])).
% 7.12/1.48  
% 7.12/1.48  fof(f66,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f21])).
% 7.12/1.48  
% 7.12/1.48  fof(f5,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f46,plain,(
% 7.12/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.12/1.48    inference(nnf_transformation,[],[f5])).
% 7.12/1.48  
% 7.12/1.48  fof(f72,plain,(
% 7.12/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f46])).
% 7.12/1.48  
% 7.12/1.48  fof(f85,plain,(
% 7.12/1.48    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f56])).
% 7.12/1.48  
% 7.12/1.48  fof(f11,axiom,(
% 7.12/1.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f19,plain,(
% 7.12/1.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f11])).
% 7.12/1.48  
% 7.12/1.48  fof(f34,plain,(
% 7.12/1.48    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(ennf_transformation,[],[f19])).
% 7.12/1.48  
% 7.12/1.48  fof(f82,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f34])).
% 7.12/1.48  
% 7.12/1.48  fof(f8,axiom,(
% 7.12/1.48    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f29,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(ennf_transformation,[],[f8])).
% 7.12/1.48  
% 7.12/1.48  fof(f30,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(flattening,[],[f29])).
% 7.12/1.48  
% 7.12/1.48  fof(f47,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(nnf_transformation,[],[f30])).
% 7.12/1.48  
% 7.12/1.48  fof(f48,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(flattening,[],[f47])).
% 7.12/1.48  
% 7.12/1.48  fof(f49,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(rectify,[],[f48])).
% 7.12/1.48  
% 7.12/1.48  fof(f50,plain,(
% 7.12/1.48    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f51,plain,(
% 7.12/1.48    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 7.12/1.48  
% 7.12/1.48  fof(f76,plain,(
% 7.12/1.48    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f51])).
% 7.12/1.48  
% 7.12/1.48  fof(f102,plain,(
% 7.12/1.48    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(equality_resolution,[],[f76])).
% 7.12/1.48  
% 7.12/1.48  fof(f9,axiom,(
% 7.12/1.48    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f31,plain,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(ennf_transformation,[],[f9])).
% 7.12/1.48  
% 7.12/1.48  fof(f80,plain,(
% 7.12/1.48    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f31])).
% 7.12/1.48  
% 7.12/1.48  fof(f10,axiom,(
% 7.12/1.48    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f20,plain,(
% 7.12/1.48    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 7.12/1.48    inference(pure_predicate_removal,[],[f10])).
% 7.12/1.48  
% 7.12/1.48  fof(f32,plain,(
% 7.12/1.48    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.12/1.48    inference(ennf_transformation,[],[f20])).
% 7.12/1.48  
% 7.12/1.48  fof(f33,plain,(
% 7.12/1.48    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.12/1.48    inference(flattening,[],[f32])).
% 7.12/1.48  
% 7.12/1.48  fof(f81,plain,(
% 7.12/1.48    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f33])).
% 7.12/1.48  
% 7.12/1.48  fof(f93,plain,(
% 7.12/1.48    v1_yellow_0(sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f91,plain,(
% 7.12/1.48    ~v2_struct_0(sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f92,plain,(
% 7.12/1.48    v5_orders_2(sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f7,axiom,(
% 7.12/1.48    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f28,plain,(
% 7.12/1.48    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 7.12/1.48    inference(ennf_transformation,[],[f7])).
% 7.12/1.48  
% 7.12/1.48  fof(f74,plain,(
% 7.12/1.48    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f28])).
% 7.12/1.48  
% 7.12/1.48  fof(f1,axiom,(
% 7.12/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f40,plain,(
% 7.12/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.48    inference(nnf_transformation,[],[f1])).
% 7.12/1.48  
% 7.12/1.48  fof(f41,plain,(
% 7.12/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.48    inference(flattening,[],[f40])).
% 7.12/1.48  
% 7.12/1.48  fof(f64,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.12/1.48    inference(cnf_transformation,[],[f41])).
% 7.12/1.48  
% 7.12/1.48  fof(f100,plain,(
% 7.12/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.12/1.48    inference(equality_resolution,[],[f64])).
% 7.12/1.48  
% 7.12/1.48  fof(f97,plain,(
% 7.12/1.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f71,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f46])).
% 7.12/1.48  
% 7.12/1.48  fof(f88,plain,(
% 7.12/1.48    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | ~r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f56])).
% 7.12/1.48  
% 7.12/1.48  fof(f13,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f37,plain,(
% 7.12/1.48    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(ennf_transformation,[],[f13])).
% 7.12/1.48  
% 7.12/1.48  fof(f57,plain,(
% 7.12/1.48    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(nnf_transformation,[],[f37])).
% 7.12/1.48  
% 7.12/1.48  fof(f90,plain,(
% 7.12/1.48    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f57])).
% 7.12/1.48  
% 7.12/1.48  fof(f99,plain,(
% 7.12/1.48    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f96,plain,(
% 7.12/1.48    v13_waybel_0(sK5,sK4)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f4,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f24,plain,(
% 7.12/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.12/1.48    inference(ennf_transformation,[],[f4])).
% 7.12/1.48  
% 7.12/1.48  fof(f25,plain,(
% 7.12/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.12/1.48    inference(flattening,[],[f24])).
% 7.12/1.48  
% 7.12/1.48  fof(f70,plain,(
% 7.12/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.12/1.48    inference(cnf_transformation,[],[f25])).
% 7.12/1.48  
% 7.12/1.48  fof(f95,plain,(
% 7.12/1.48    ~v1_xboole_0(sK5)),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  fof(f3,axiom,(
% 7.12/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 7.12/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.12/1.48  
% 7.12/1.48  fof(f22,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(ennf_transformation,[],[f3])).
% 7.12/1.48  
% 7.12/1.48  fof(f23,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(flattening,[],[f22])).
% 7.12/1.48  
% 7.12/1.48  fof(f42,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(nnf_transformation,[],[f23])).
% 7.12/1.48  
% 7.12/1.48  fof(f43,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(flattening,[],[f42])).
% 7.12/1.48  
% 7.12/1.48  fof(f44,plain,(
% 7.12/1.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 7.12/1.48    introduced(choice_axiom,[])).
% 7.12/1.48  
% 7.12/1.48  fof(f45,plain,(
% 7.12/1.48    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 7.12/1.48  
% 7.12/1.48  fof(f69,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f45])).
% 7.12/1.48  
% 7.12/1.48  fof(f67,plain,(
% 7.12/1.48    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f45])).
% 7.12/1.48  
% 7.12/1.48  fof(f89,plain,(
% 7.12/1.48    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.48    inference(cnf_transformation,[],[f57])).
% 7.12/1.48  
% 7.12/1.48  fof(f104,plain,(
% 7.12/1.48    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 7.12/1.48    inference(equality_resolution,[],[f89])).
% 7.12/1.48  
% 7.12/1.48  fof(f98,plain,(
% 7.12/1.48    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 7.12/1.48    inference(cnf_transformation,[],[f62])).
% 7.12/1.48  
% 7.12/1.48  cnf(c_25,plain,
% 7.12/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.12/1.48      | ~ v13_waybel_0(X3,X0)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.12/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.12/1.48      | ~ r2_hidden(X1,X3)
% 7.12/1.48      | r2_hidden(X2,X3)
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_33,negated_conjecture,
% 7.12/1.48      ( l1_orders_2(sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_692,plain,
% 7.12/1.48      ( ~ r1_orders_2(X0,X1,X2)
% 7.12/1.48      | ~ v13_waybel_0(X3,X0)
% 7.12/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.12/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.12/1.48      | ~ r2_hidden(X1,X3)
% 7.12/1.48      | r2_hidden(X2,X3)
% 7.12/1.48      | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_693,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ v13_waybel_0(X2,sK4)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(X0,X2)
% 7.12/1.48      | r2_hidden(X1,X2) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_692]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_10,plain,
% 7.12/1.48      ( m1_subset_1(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ r2_hidden(X0,X2) ),
% 7.12/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_709,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ v13_waybel_0(X2,sK4)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(X0,X2)
% 7.12/1.48      | r2_hidden(X1,X2) ),
% 7.12/1.48      inference(forward_subsumption_resolution,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_693,c_10]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_12440,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ v13_waybel_0(u1_struct_0(sK4),sK4)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | r2_hidden(X0,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_709]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_21403,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
% 7.12/1.48      | ~ v13_waybel_0(u1_struct_0(sK4),sK4)
% 7.12/1.48      | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_12440]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5870,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ v13_waybel_0(sK5,sK4)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | r2_hidden(X0,sK5)
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_709]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_11153,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
% 7.12/1.48      | ~ v13_waybel_0(sK5,sK4)
% 7.12/1.48      | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),sK5)
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_5870]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ r2_hidden(X2,X0)
% 7.12/1.48      | r2_hidden(X2,X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_8,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_292,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.12/1.48      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_293,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_292]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_366,plain,
% 7.12/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_3,c_293]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5860,plain,
% 7.12/1.48      ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
% 7.12/1.48      | ~ r1_tarski(sK5,X0) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_366]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_10178,plain,
% 7.12/1.48      ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
% 7.12/1.48      | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_5860]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2234,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.12/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_23,plain,
% 7.12/1.48      ( v13_waybel_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.48      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 7.12/1.48      | ~ l1_orders_2(X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_773,plain,
% 7.12/1.48      ( v13_waybel_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.48      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 7.12/1.48      | sK4 != X1 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_774,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_773]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2221,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) = iProver_top
% 7.12/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | m1_subset_1(sK3(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_19,plain,
% 7.12/1.48      ( r2_lattice3(X0,k1_xboole_0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_732,plain,
% 7.12/1.48      ( r2_lattice3(X0,k1_xboole_0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.12/1.48      | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_733,plain,
% 7.12/1.48      ( r2_lattice3(sK4,k1_xboole_0,X0)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_732]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_15,plain,
% 7.12/1.48      ( ~ r2_lattice3(X0,X1,X2)
% 7.12/1.48      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.12/1.48      | ~ r1_yellow_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_17,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_226,plain,
% 7.12/1.48      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ r1_yellow_0(X0,X1)
% 7.12/1.48      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.12/1.48      | ~ r2_lattice3(X0,X1,X2)
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_15,c_17]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_227,plain,
% 7.12/1.48      ( ~ r2_lattice3(X0,X1,X2)
% 7.12/1.48      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.12/1.48      | ~ r1_yellow_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_226]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_18,plain,
% 7.12/1.48      ( r1_yellow_0(X0,k1_xboole_0)
% 7.12/1.48      | v2_struct_0(X0)
% 7.12/1.48      | ~ v5_orders_2(X0)
% 7.12/1.48      | ~ v1_yellow_0(X0)
% 7.12/1.48      | ~ l1_orders_2(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_34,negated_conjecture,
% 7.12/1.48      ( v1_yellow_0(sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_517,plain,
% 7.12/1.48      ( r1_yellow_0(X0,k1_xboole_0)
% 7.12/1.48      | v2_struct_0(X0)
% 7.12/1.48      | ~ v5_orders_2(X0)
% 7.12/1.48      | ~ l1_orders_2(X0)
% 7.12/1.48      | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_518,plain,
% 7.12/1.48      ( r1_yellow_0(sK4,k1_xboole_0)
% 7.12/1.48      | v2_struct_0(sK4)
% 7.12/1.48      | ~ v5_orders_2(sK4)
% 7.12/1.48      | ~ l1_orders_2(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_517]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_36,negated_conjecture,
% 7.12/1.48      ( ~ v2_struct_0(sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_35,negated_conjecture,
% 7.12/1.48      ( v5_orders_2(sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_72,plain,
% 7.12/1.48      ( r1_yellow_0(sK4,k1_xboole_0)
% 7.12/1.48      | v2_struct_0(sK4)
% 7.12/1.48      | ~ v5_orders_2(sK4)
% 7.12/1.48      | ~ v1_yellow_0(sK4)
% 7.12/1.48      | ~ l1_orders_2(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_520,plain,
% 7.12/1.48      ( r1_yellow_0(sK4,k1_xboole_0) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_518,c_36,c_35,c_34,c_33,c_72]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_567,plain,
% 7.12/1.48      ( ~ r2_lattice3(X0,X1,X2)
% 7.12/1.48      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.12/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.12/1.48      | ~ l1_orders_2(X0)
% 7.12/1.48      | sK4 != X0
% 7.12/1.48      | k1_xboole_0 != X1 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_227,c_520]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_568,plain,
% 7.12/1.48      ( ~ r2_lattice3(sK4,k1_xboole_0,X0)
% 7.12/1.48      | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | ~ l1_orders_2(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_567]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_572,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ r2_lattice3(sK4,k1_xboole_0,X0) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_568,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_573,plain,
% 7.12/1.48      ( ~ r2_lattice3(sK4,k1_xboole_0,X0)
% 7.12/1.48      | r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_572]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_830,plain,
% 7.12/1.48      ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(backward_subsumption_resolution,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_733,c_573]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2218,plain,
% 7.12/1.48      ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),X0) = iProver_top
% 7.12/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_11,plain,
% 7.12/1.48      ( ~ l1_orders_2(X0)
% 7.12/1.48      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_753,plain,
% 7.12/1.48      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_754,plain,
% 7.12/1.48      ( k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_753]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2259,plain,
% 7.12/1.48      ( r1_orders_2(sK4,k3_yellow_0(sK4),X0) = iProver_top
% 7.12/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(light_normalisation,[status(thm)],[c_2218,c_754]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2225,plain,
% 7.12/1.48      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.12/1.48      | v13_waybel_0(X2,sK4) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.12/1.48      | r2_hidden(X1,X2) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4053,plain,
% 7.12/1.48      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.12/1.48      | v13_waybel_0(X2,sK4) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.12/1.48      | r2_hidden(X1,X2) = iProver_top
% 7.12/1.48      | r1_tarski(X2,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2234,c_2225]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5405,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
% 7.12/1.48      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2259,c_4053]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5445,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) != iProver_top
% 7.12/1.48      | v13_waybel_0(X1,sK4) = iProver_top
% 7.12/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,X1),X0) = iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
% 7.12/1.48      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2221,c_5405]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6610,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) != iProver_top
% 7.12/1.48      | v13_waybel_0(X1,sK4) = iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,X1),X0) = iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
% 7.12/1.48      | r1_tarski(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2234,c_5445]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1,plain,
% 7.12/1.48      ( r1_tarski(X0,X0) ),
% 7.12/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2235,plain,
% 7.12/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_30,negated_conjecture,
% 7.12/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 7.12/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2231,plain,
% 7.12/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2232,plain,
% 7.12/1.48      ( m1_subset_1(X0,X1) = iProver_top
% 7.12/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,X2) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3716,plain,
% 7.12/1.48      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2231,c_2232]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5441,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) != iProver_top
% 7.12/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.12/1.48      | r2_hidden(X1,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),X0) != iProver_top
% 7.12/1.48      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_3716,c_5405]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5717,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4) != iProver_top
% 7.12/1.48      | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2235,c_5441]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_9,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2939,plain,
% 7.12/1.48      ( r1_tarski(sK5,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_9,c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3453,plain,
% 7.12/1.48      ( r2_hidden(X0,u1_struct_0(sK4)) | ~ r2_hidden(X0,sK5) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_366,c_2939]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3454,plain,
% 7.12/1.48      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_3453]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6094,plain,
% 7.12/1.48      ( r2_hidden(X0,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(X0,u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_5717,c_3454]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6095,plain,
% 7.12/1.48      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_6094]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_20,plain,
% 7.12/1.48      ( v13_waybel_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.48      | ~ r2_hidden(sK3(X1,X0),X0)
% 7.12/1.48      | ~ l1_orders_2(X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_803,plain,
% 7.12/1.48      ( v13_waybel_0(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.48      | ~ r2_hidden(sK3(X1,X0),X0)
% 7.12/1.48      | sK4 != X1 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_804,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(sK3(sK4,X0),X0) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_803]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2219,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) = iProver_top
% 7.12/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,X0),X0) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2922,plain,
% 7.12/1.48      ( v13_waybel_0(X0,sK4) = iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,X0),X0) != iProver_top
% 7.12/1.48      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2234,c_2219]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6103,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top
% 7.12/1.48      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_6095,c_2922]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3582,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4)
% 7.12/1.48      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_804,c_3453]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2483,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2648,plain,
% 7.12/1.48      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2483]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2649,plain,
% 7.12/1.48      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3922,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4)
% 7.12/1.48      | ~ r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_3582,c_2648,c_2649]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3924,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_3922]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6921,plain,
% 7.12/1.48      ( r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top
% 7.12/1.48      | v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_6103,c_3924]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6922,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 7.12/1.48      | r2_hidden(sK3(sK4,u1_struct_0(sK4)),sK5) != iProver_top ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_6921]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7663,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4) = iProver_top
% 7.12/1.48      | v13_waybel_0(sK5,sK4) != iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.12/1.48      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_6610,c_6922]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7723,plain,
% 7.12/1.48      ( v13_waybel_0(u1_struct_0(sK4),sK4)
% 7.12/1.48      | ~ v13_waybel_0(sK5,sK4)
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_7663]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_744,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK4 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_745,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_744]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2223,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2495,plain,
% 7.12/1.48      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_754,c_2223]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_26,plain,
% 7.12/1.48      ( v1_subset_1(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | X0 = X1 ),
% 7.12/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_372,plain,
% 7.12/1.48      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_26,c_293]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_28,negated_conjecture,
% 7.12/1.48      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.12/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_296,plain,
% 7.12/1.48      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.12/1.48      inference(prop_impl,[status(thm)],[c_28]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_533,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | ~ r1_tarski(X0,X1)
% 7.12/1.48      | X1 = X0
% 7.12/1.48      | u1_struct_0(sK4) != X1
% 7.12/1.48      | sK5 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_372,c_296]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_534,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.12/1.48      | u1_struct_0(sK4) = sK5 ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_533]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2227,plain,
% 7.12/1.48      ( u1_struct_0(sK4) = sK5
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.12/1.48      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_43,plain,
% 7.12/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_535,plain,
% 7.12/1.48      ( u1_struct_0(sK4) = sK5
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.12/1.48      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2488,plain,
% 7.12/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | r1_tarski(sK5,u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2489,plain,
% 7.12/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_2488]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6268,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.12/1.48      | u1_struct_0(sK4) = sK5 ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_2227,c_43,c_535,c_2489]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6269,plain,
% 7.12/1.48      ( u1_struct_0(sK4) = sK5
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_6268]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4054,plain,
% 7.12/1.48      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.12/1.48      | v13_waybel_0(sK5,sK4) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(X1,sK5) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2231,c_2225]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_31,negated_conjecture,
% 7.12/1.48      ( v13_waybel_0(sK5,sK4) ),
% 7.12/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_954,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(X0,X2)
% 7.12/1.48      | r2_hidden(X1,X2)
% 7.12/1.48      | sK5 != X2
% 7.12/1.48      | sK4 != sK4 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_31,c_709]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_955,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(X0,sK5)
% 7.12/1.48      | r2_hidden(X1,sK5) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_954]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_957,plain,
% 7.12/1.48      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ r2_hidden(X0,sK5)
% 7.12/1.48      | r2_hidden(X1,sK5) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_955,c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_958,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(X0,sK5)
% 7.12/1.48      | r2_hidden(X1,sK5) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_957]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_959,plain,
% 7.12/1.48      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(X1,sK5) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4098,plain,
% 7.12/1.48      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.12/1.48      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) != iProver_top
% 7.12/1.48      | r2_hidden(X1,sK5) = iProver_top ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_4054,c_959]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4107,plain,
% 7.12/1.48      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) = iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2259,c_4098]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6276,plain,
% 7.12/1.48      ( u1_struct_0(sK4) = sK5
% 7.12/1.48      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_6269,c_4107]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_93,plain,
% 7.12/1.48      ( ~ l1_orders_2(sK4)
% 7.12/1.48      | k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3103,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ v13_waybel_0(sK5,sK4)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(X0,sK5)
% 7.12/1.48      | r2_hidden(X1,sK5) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_709,c_30]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3208,plain,
% 7.12/1.48      ( ~ r1_orders_2(sK4,X0,X1)
% 7.12/1.48      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(X0,sK5)
% 7.12/1.48      | r2_hidden(X1,sK5) ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_3103,c_30,c_955]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3232,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.12/1.48      | r2_hidden(X0,sK5)
% 7.12/1.48      | ~ r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_3208,c_830]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3233,plain,
% 7.12/1.48      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) = iProver_top
% 7.12/1.48      | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_3232]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1591,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.12/1.48      theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3266,plain,
% 7.12/1.48      ( m1_subset_1(X0,X1)
% 7.12/1.48      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | X1 != u1_struct_0(sK4)
% 7.12/1.48      | X0 != k3_yellow_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1591]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3642,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),X0)
% 7.12/1.48      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | X0 != u1_struct_0(sK4)
% 7.12/1.48      | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_3266]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4734,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5)
% 7.12/1.48      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
% 7.12/1.48      | sK5 != u1_struct_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_3642]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4736,plain,
% 7.12/1.48      ( k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
% 7.12/1.48      | sK5 != u1_struct_0(sK4)
% 7.12/1.48      | m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5) = iProver_top
% 7.12/1.48      | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_4734]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.12/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_32,negated_conjecture,
% 7.12/1.48      ( ~ v1_xboole_0(sK5) ),
% 7.12/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_502,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK5 != X1 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_7,c_32]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_503,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_502]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4735,plain,
% 7.12/1.48      ( ~ m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5)
% 7.12/1.48      | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_503]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4738,plain,
% 7.12/1.48      ( m1_subset_1(k1_yellow_0(sK4,k1_xboole_0),sK5) != iProver_top
% 7.12/1.48      | r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_4735]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1587,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1586,plain,( X0 = X0 ),theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4846,plain,
% 7.12/1.48      ( X0 != X1 | X1 = X0 ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_1587,c_1586]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2948,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 7.12/1.48      inference(backward_subsumption_resolution,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_2939,c_534]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6703,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5) | sK5 = u1_struct_0(sK4) ),
% 7.12/1.48      inference(resolution,[status(thm)],[c_4846,c_2948]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6704,plain,
% 7.12/1.48      ( sK5 = u1_struct_0(sK4)
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_6703]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7355,plain,
% 7.12/1.48      ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 7.12/1.48      | r2_hidden(X0,sK5) = iProver_top ),
% 7.12/1.48      inference(global_propositional_subsumption,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_6276,c_33,c_93,c_2495,c_3233,c_4107,c_4736,c_4738,
% 7.12/1.48                 c_6704]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_7369,plain,
% 7.12/1.48      ( r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 7.12/1.48      inference(superposition,[status(thm)],[c_2495,c_7355]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_4,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 7.12/1.48      | ~ r2_hidden(sK0(X1,X0,X2),X0)
% 7.12/1.48      | X2 = X0 ),
% 7.12/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_367,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ r2_hidden(sK0(X1,X2,X0),X0)
% 7.12/1.48      | ~ r2_hidden(sK0(X1,X2,X0),X2)
% 7.12/1.48      | ~ r1_tarski(X2,X1)
% 7.12/1.48      | X0 = X2 ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_4,c_293]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1196,plain,
% 7.12/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.12/1.48      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1197,plain,
% 7.12/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.48      inference(renaming,[status(thm)],[c_1196]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1249,plain,
% 7.12/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.12/1.48      | ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.12/1.48      | ~ r1_tarski(X2,X0)
% 7.12/1.48      | ~ r1_tarski(X1,X0)
% 7.12/1.48      | X2 = X1 ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_367,c_1197]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5329,plain,
% 7.12/1.48      ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),sK5)
% 7.12/1.48      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.12/1.48      | sK5 = u1_struct_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1249]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5324,plain,
% 7.12/1.48      ( r1_orders_2(sK4,k1_yellow_0(sK4,k1_xboole_0),sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5))
% 7.12/1.48      | ~ m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4)) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_830]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1589,plain,
% 7.12/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.12/1.48      theory(equality) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2687,plain,
% 7.12/1.48      ( r2_hidden(X0,X1)
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | X0 != k3_yellow_0(sK4)
% 7.12/1.48      | X1 != sK5 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1589]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3152,plain,
% 7.12/1.48      ( r2_hidden(X0,sK5)
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | X0 != k3_yellow_0(sK4)
% 7.12/1.48      | sK5 != sK5 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2687]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_5128,plain,
% 7.12/1.48      ( r2_hidden(k1_yellow_0(sK4,k1_xboole_0),sK5)
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | k1_yellow_0(sK4,k1_xboole_0) != k3_yellow_0(sK4)
% 7.12/1.48      | sK5 != sK5 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_3152]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_6,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.12/1.48      | m1_subset_1(sK0(X1,X0,X2),X1)
% 7.12/1.48      | X2 = X0 ),
% 7.12/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_369,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.48      | m1_subset_1(sK0(X1,X2,X0),X1)
% 7.12/1.48      | ~ r1_tarski(X2,X1)
% 7.12/1.48      | X0 = X2 ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_6,c_293]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_1251,plain,
% 7.12/1.48      ( m1_subset_1(sK0(X0,X1,X2),X0)
% 7.12/1.48      | ~ r1_tarski(X2,X0)
% 7.12/1.48      | ~ r1_tarski(X1,X0)
% 7.12/1.48      | X2 = X1 ),
% 7.12/1.48      inference(bin_hyper_res,[status(thm)],[c_369,c_1197]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2574,plain,
% 7.12/1.48      ( m1_subset_1(sK0(X0,u1_struct_0(sK4),sK5),X0)
% 7.12/1.48      | ~ r1_tarski(u1_struct_0(sK4),X0)
% 7.12/1.48      | ~ r1_tarski(sK5,X0)
% 7.12/1.48      | sK5 = u1_struct_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1251]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_3135,plain,
% 7.12/1.48      ( m1_subset_1(sK0(u1_struct_0(sK4),u1_struct_0(sK4),sK5),u1_struct_0(sK4))
% 7.12/1.48      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 7.12/1.48      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.12/1.48      | sK5 = u1_struct_0(sK4) ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_2574]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2652,plain,
% 7.12/1.48      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_2649]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2650,plain,
% 7.12/1.48      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.12/1.48      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_2648]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_2635,plain,
% 7.12/1.48      ( sK5 = sK5 ),
% 7.12/1.48      inference(instantiation,[status(thm)],[c_1586]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_27,plain,
% 7.12/1.48      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 7.12/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_29,negated_conjecture,
% 7.12/1.48      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.12/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_294,plain,
% 7.12/1.48      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.12/1.48      inference(prop_impl,[status(thm)],[c_29]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_546,plain,
% 7.12/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | u1_struct_0(sK4) != X0
% 7.12/1.48      | sK5 != X0 ),
% 7.12/1.48      inference(resolution_lifted,[status(thm)],[c_27,c_294]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_547,plain,
% 7.12/1.48      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.12/1.48      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.12/1.48      | sK5 != u1_struct_0(sK4) ),
% 7.12/1.48      inference(unflattening,[status(thm)],[c_546]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(c_548,plain,
% 7.12/1.48      ( sK5 != u1_struct_0(sK4)
% 7.12/1.48      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.12/1.48      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.12/1.48      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 7.12/1.48  
% 7.12/1.48  cnf(contradiction,plain,
% 7.12/1.48      ( $false ),
% 7.12/1.48      inference(minisat,
% 7.12/1.48                [status(thm)],
% 7.12/1.48                [c_21403,c_11153,c_10178,c_7723,c_7369,c_6703,c_5329,
% 7.12/1.48                 c_5324,c_5128,c_3135,c_2652,c_2649,c_2650,c_2648,c_2635,
% 7.12/1.48                 c_2488,c_548,c_93,c_30,c_31,c_33]) ).
% 7.12/1.48  
% 7.12/1.48  
% 7.12/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.48  
% 7.12/1.48  ------                               Statistics
% 7.12/1.48  
% 7.12/1.48  ------ Selected
% 7.12/1.48  
% 7.12/1.48  total_time:                             0.503
% 7.12/1.48  
%------------------------------------------------------------------------------
