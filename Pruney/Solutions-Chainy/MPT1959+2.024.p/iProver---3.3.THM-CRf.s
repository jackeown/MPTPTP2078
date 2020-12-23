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
% DateTime   : Thu Dec  3 12:28:29 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  308 (3572 expanded)
%              Number of clauses        :  216 ( 964 expanded)
%              Number of leaves         :   26 ( 740 expanded)
%              Depth                    :   31
%              Number of atoms          : 1093 (29071 expanded)
%              Number of equality atoms :  386 (1211 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f40,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f56,plain,(
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
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f58,plain,(
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

fof(f57,plain,
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
        & v4_orders_2(X0)
        & v3_orders_2(X0)
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
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f56,f58,f57])).

fof(f90,plain,(
    v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).

fof(f76,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f95,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f46])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( v1_yellow_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_507,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_508,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_77,plain,
    ( r1_yellow_0(sK4,k1_xboole_0)
    | v2_struct_0(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_510,plain,
    ( r1_yellow_0(sK4,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_36,c_33,c_32,c_31,c_77])).

cnf(c_3201,plain,
    ( r1_yellow_0(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3214,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3215,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4602,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3214,c_3215])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_281])).

cnf(c_3202,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_6478,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4602,c_3202])).

cnf(c_16631,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3214,c_6478])).

cnf(c_23,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_610,plain,
    ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_611,plain,
    ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_35,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_615,plain,
    ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_36,c_35,c_34,c_31])).

cnf(c_3199,plain,
    ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_12,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_795,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_796,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_3193,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_36,c_35,c_34,c_31])).

cnf(c_3198,plain,
    ( k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_3601,plain,
    ( k1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X0))) = k1_yellow_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3193,c_3198])).

cnf(c_14,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_770,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ r1_yellow_0(X0,X2)
    | ~ r1_tarski(X1,X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_771,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1))
    | ~ r1_yellow_0(sK4,X1)
    | ~ r1_yellow_0(sK4,X0)
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_3195,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1)) = iProver_top
    | r1_yellow_0(sK4,X1) != iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_5084,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1)) = iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_3195])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3207,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_730,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_731,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ v13_waybel_0(X2,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_747,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ v13_waybel_0(X2,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_731,c_9])).

cnf(c_3197,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_5165,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_3197])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_972,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK5 != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_747])).

cnf(c_973,plain,
    ( ~ r1_orders_2(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5) ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_974,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_5244,plain,
    ( r1_orders_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5165,c_45,c_974])).

cnf(c_5745,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_5244])).

cnf(c_6345,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_5745])).

cnf(c_16779,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16631,c_6345])).

cnf(c_3625,plain,
    ( ~ r2_hidden(sK0(X0,sK5),sK5)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4422,plain,
    ( ~ r2_hidden(sK0(sK5,sK5),sK5)
    | r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3625])).

cnf(c_4425,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5) != iProver_top
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4422])).

cnf(c_3626,plain,
    ( r2_hidden(sK0(X0,sK5),X0)
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4420,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5)
    | r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_4429,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5) = iProver_top
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4420])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3211,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4610,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3193,c_3211])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_43,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_365,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_24,c_281])).

cnf(c_26,negated_conjecture,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_284,plain,
    ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_576,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK4) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_284])).

cnf(c_577,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_578,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_797,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_3418,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
    | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3419,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3418])).

cnf(c_2527,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3259,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_3560,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(sK5)
    | sK5 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_3561,plain,
    ( sK5 != u1_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3560])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3747,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3207,c_3209])).

cnf(c_3567,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_4342,plain,
    ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3567])).

cnf(c_4343,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4342])).

cnf(c_2524,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4636,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_2525,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3653,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_4640,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3653])).

cnf(c_5233,plain,
    ( u1_struct_0(sK4) != sK5
    | sK5 = u1_struct_0(sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4640])).

cnf(c_5861,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4610,c_43,c_578,c_797,c_3419,c_3561,c_3747,c_4343,c_4636,c_5233])).

cnf(c_3210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3208,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4712,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_3208])).

cnf(c_6691,plain,
    ( m1_subset_1(k1_yellow_0(sK4,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5861,c_4712])).

cnf(c_9516,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK4),X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6691,c_3211])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7588,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),X1)
    | ~ r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7590,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7588])).

cnf(c_9877,plain,
    ( r1_tarski(u1_struct_0(sK4),X1) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9516,c_43,c_578,c_797,c_3419,c_3561,c_3747,c_4343,c_4636,c_5233,c_7590])).

cnf(c_9878,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9877])).

cnf(c_13,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_788,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_789,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_3194,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_3600,plain,
    ( k1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) = k3_yellow_0(sK4) ),
    inference(superposition,[status(thm)],[c_3194,c_3198])).

cnf(c_5072,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_3195])).

cnf(c_42,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_82,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_84,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_3267,plain,
    ( r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)))
    | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_3268,plain,
    ( r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) = iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3267])).

cnf(c_5459,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5072,c_42,c_84,c_3268])).

cnf(c_5460,plain,
    ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5459])).

cnf(c_5468,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5460,c_5244])).

cnf(c_6186,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5468,c_42,c_84])).

cnf(c_16778,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16631,c_6186])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_112,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_25,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_27,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_282,plain,
    ( v1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_282])).

cnf(c_590,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5)
    | sK5 != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_591,plain,
    ( sK5 != u1_struct_0(sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2529,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3721,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_4228,plain,
    ( m1_subset_1(u1_struct_0(sK4),X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK4))
    | u1_struct_0(sK4) != sK5 ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_5002,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK4) != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4228])).

cnf(c_5003,plain,
    ( u1_struct_0(sK4) != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5002])).

cnf(c_5588,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_361,plain,
    ( m1_subset_1(sK1(X0,X1),X0)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_281])).

cnf(c_3203,plain,
    ( X0 = X1
    | m1_subset_1(sK1(X1,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_6007,plain,
    ( k1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),X0))) = sK1(u1_struct_0(sK4),X0)
    | u1_struct_0(sK4) = X0
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3203,c_3198])).

cnf(c_7542,plain,
    ( k1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) = sK1(u1_struct_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_3747,c_6007])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_804,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_805,plain,
    ( k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_4152,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_3195])).

cnf(c_37,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( v5_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( v1_yellow_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_76,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_yellow_0(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_78,plain,
    ( r1_yellow_0(sK4,k1_xboole_0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v5_orders_2(sK4) != iProver_top
    | v1_yellow_0(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_4161,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4152,c_37,c_40,c_41,c_42,c_78])).

cnf(c_4162,plain,
    ( r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4161])).

cnf(c_7873,plain,
    ( u1_struct_0(sK4) = sK5
    | r1_orders_2(sK4,k3_yellow_0(sK4),sK1(u1_struct_0(sK4),sK5)) = iProver_top
    | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7542,c_4162])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_360,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_281])).

cnf(c_3640,plain,
    ( ~ r2_hidden(sK1(X0,sK5),sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_4407,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4))
    | sK5 = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3640])).

cnf(c_4411,plain,
    ( sK5 = u1_struct_0(sK4)
    | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4407])).

cnf(c_3200,plain,
    ( sK5 != u1_struct_0(sK4)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_3296,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3704,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3296])).

cnf(c_3705,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3704])).

cnf(c_3397,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3817,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3397])).

cnf(c_3820,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3817])).

cnf(c_3398,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3815,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3398])).

cnf(c_3824,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3815])).

cnf(c_5755,plain,
    ( sK5 != u1_struct_0(sK4)
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_591,c_3705,c_3820,c_3824])).

cnf(c_5251,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4162,c_5244])).

cnf(c_6084,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5251,c_797])).

cnf(c_7863,plain,
    ( u1_struct_0(sK4) = sK5
    | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7542,c_6084])).

cnf(c_8142,plain,
    ( u1_struct_0(sK4) = sK5
    | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7873,c_578,c_3747,c_4411,c_5755,c_7863])).

cnf(c_8146,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3199,c_8142])).

cnf(c_7875,plain,
    ( u1_struct_0(sK4) = sK5
    | m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7542,c_3193])).

cnf(c_8475,plain,
    ( u1_struct_0(sK4) = sK5
    | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8146,c_7875])).

cnf(c_16801,plain,
    ( u1_struct_0(sK4) = sK5
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16631,c_8475])).

cnf(c_17252,plain,
    ( r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r1_yellow_0(sK4,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16778,c_112,c_591,c_3705,c_3820,c_3824,c_4636,c_5233,c_16801])).

cnf(c_17253,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17252])).

cnf(c_17259,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK4),sK5) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9878,c_17253])).

cnf(c_278,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_1292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK4) = sK5
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_279,c_577])).

cnf(c_1293,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(unflattening,[status(thm)],[c_1292])).

cnf(c_1295,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5)
    | u1_struct_0(sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1293,c_28])).

cnf(c_3188,plain,
    ( u1_struct_0(sK4) = sK5
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1295])).

cnf(c_5249,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,X1) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3195,c_5244])).

cnf(c_6280,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,X1) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X1),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3193,c_5249])).

cnf(c_6337,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_yellow_0(sK4,X1) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6084,c_6280])).

cnf(c_13375,plain,
    ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3747,c_6337])).

cnf(c_3573,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3577,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3573])).

cnf(c_3572,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3579,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3572])).

cnf(c_4169,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_6330,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4169])).

cnf(c_6332,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6330])).

cnf(c_6331,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_6334,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6331])).

cnf(c_13400,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13375,c_112,c_3577,c_3579,c_6332,c_6334])).

cnf(c_13401,plain,
    ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_13400])).

cnf(c_13404,plain,
    ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | m1_subset_1(k1_yellow_0(sK4,u1_struct_0(sK4)),X0) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13401,c_4712])).

cnf(c_13483,plain,
    ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(k1_yellow_0(sK4,u1_struct_0(sK4)),X0) = iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13404,c_3209])).

cnf(c_3213,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13770,plain,
    ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
    | r1_yellow_0(sK4,sK5) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_yellow_0(sK4,u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
    | r1_tarski(sK5,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13483,c_3213])).

cnf(c_16881,plain,
    ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13770,c_112,c_591,c_3705,c_3820,c_3824,c_4636,c_5233,c_16801])).

cnf(c_16885,plain,
    ( u1_struct_0(sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_3188,c_16881])).

cnf(c_17264,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17259,c_16885])).

cnf(c_17610,plain,
    ( r1_yellow_0(sK4,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16779,c_4425,c_4429,c_17264])).

cnf(c_17616,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_17610])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17616,c_112])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:34:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.74/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.51  
% 7.74/1.51  ------  iProver source info
% 7.74/1.51  
% 7.74/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.51  git: non_committed_changes: false
% 7.74/1.51  git: last_make_outside_of_git: false
% 7.74/1.51  
% 7.74/1.51  ------ 
% 7.74/1.51  
% 7.74/1.51  ------ Input Options
% 7.74/1.51  
% 7.74/1.51  --out_options                           all
% 7.74/1.51  --tptp_safe_out                         true
% 7.74/1.51  --problem_path                          ""
% 7.74/1.51  --include_path                          ""
% 7.74/1.51  --clausifier                            res/vclausify_rel
% 7.74/1.51  --clausifier_options                    ""
% 7.74/1.51  --stdin                                 false
% 7.74/1.51  --stats_out                             all
% 7.74/1.51  
% 7.74/1.51  ------ General Options
% 7.74/1.51  
% 7.74/1.51  --fof                                   false
% 7.74/1.51  --time_out_real                         305.
% 7.74/1.51  --time_out_virtual                      -1.
% 7.74/1.51  --symbol_type_check                     false
% 7.74/1.51  --clausify_out                          false
% 7.74/1.51  --sig_cnt_out                           false
% 7.74/1.51  --trig_cnt_out                          false
% 7.74/1.51  --trig_cnt_out_tolerance                1.
% 7.74/1.51  --trig_cnt_out_sk_spl                   false
% 7.74/1.51  --abstr_cl_out                          false
% 7.74/1.51  
% 7.74/1.51  ------ Global Options
% 7.74/1.51  
% 7.74/1.51  --schedule                              default
% 7.74/1.51  --add_important_lit                     false
% 7.74/1.51  --prop_solver_per_cl                    1000
% 7.74/1.51  --min_unsat_core                        false
% 7.74/1.51  --soft_assumptions                      false
% 7.74/1.51  --soft_lemma_size                       3
% 7.74/1.51  --prop_impl_unit_size                   0
% 7.74/1.51  --prop_impl_unit                        []
% 7.74/1.51  --share_sel_clauses                     true
% 7.74/1.51  --reset_solvers                         false
% 7.74/1.51  --bc_imp_inh                            [conj_cone]
% 7.74/1.51  --conj_cone_tolerance                   3.
% 7.74/1.51  --extra_neg_conj                        none
% 7.74/1.51  --large_theory_mode                     true
% 7.74/1.51  --prolific_symb_bound                   200
% 7.74/1.51  --lt_threshold                          2000
% 7.74/1.51  --clause_weak_htbl                      true
% 7.74/1.51  --gc_record_bc_elim                     false
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing Options
% 7.74/1.51  
% 7.74/1.51  --preprocessing_flag                    true
% 7.74/1.51  --time_out_prep_mult                    0.1
% 7.74/1.51  --splitting_mode                        input
% 7.74/1.51  --splitting_grd                         true
% 7.74/1.51  --splitting_cvd                         false
% 7.74/1.51  --splitting_cvd_svl                     false
% 7.74/1.51  --splitting_nvd                         32
% 7.74/1.51  --sub_typing                            true
% 7.74/1.51  --prep_gs_sim                           true
% 7.74/1.51  --prep_unflatten                        true
% 7.74/1.51  --prep_res_sim                          true
% 7.74/1.51  --prep_upred                            true
% 7.74/1.51  --prep_sem_filter                       exhaustive
% 7.74/1.51  --prep_sem_filter_out                   false
% 7.74/1.51  --pred_elim                             true
% 7.74/1.51  --res_sim_input                         true
% 7.74/1.51  --eq_ax_congr_red                       true
% 7.74/1.51  --pure_diseq_elim                       true
% 7.74/1.51  --brand_transform                       false
% 7.74/1.51  --non_eq_to_eq                          false
% 7.74/1.51  --prep_def_merge                        true
% 7.74/1.51  --prep_def_merge_prop_impl              false
% 7.74/1.51  --prep_def_merge_mbd                    true
% 7.74/1.51  --prep_def_merge_tr_red                 false
% 7.74/1.51  --prep_def_merge_tr_cl                  false
% 7.74/1.51  --smt_preprocessing                     true
% 7.74/1.51  --smt_ac_axioms                         fast
% 7.74/1.51  --preprocessed_out                      false
% 7.74/1.51  --preprocessed_stats                    false
% 7.74/1.51  
% 7.74/1.51  ------ Abstraction refinement Options
% 7.74/1.51  
% 7.74/1.51  --abstr_ref                             []
% 7.74/1.51  --abstr_ref_prep                        false
% 7.74/1.51  --abstr_ref_until_sat                   false
% 7.74/1.51  --abstr_ref_sig_restrict                funpre
% 7.74/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.51  --abstr_ref_under                       []
% 7.74/1.51  
% 7.74/1.51  ------ SAT Options
% 7.74/1.51  
% 7.74/1.51  --sat_mode                              false
% 7.74/1.51  --sat_fm_restart_options                ""
% 7.74/1.51  --sat_gr_def                            false
% 7.74/1.51  --sat_epr_types                         true
% 7.74/1.51  --sat_non_cyclic_types                  false
% 7.74/1.51  --sat_finite_models                     false
% 7.74/1.51  --sat_fm_lemmas                         false
% 7.74/1.51  --sat_fm_prep                           false
% 7.74/1.51  --sat_fm_uc_incr                        true
% 7.74/1.51  --sat_out_model                         small
% 7.74/1.51  --sat_out_clauses                       false
% 7.74/1.51  
% 7.74/1.51  ------ QBF Options
% 7.74/1.51  
% 7.74/1.51  --qbf_mode                              false
% 7.74/1.51  --qbf_elim_univ                         false
% 7.74/1.51  --qbf_dom_inst                          none
% 7.74/1.51  --qbf_dom_pre_inst                      false
% 7.74/1.51  --qbf_sk_in                             false
% 7.74/1.51  --qbf_pred_elim                         true
% 7.74/1.51  --qbf_split                             512
% 7.74/1.51  
% 7.74/1.51  ------ BMC1 Options
% 7.74/1.51  
% 7.74/1.51  --bmc1_incremental                      false
% 7.74/1.51  --bmc1_axioms                           reachable_all
% 7.74/1.51  --bmc1_min_bound                        0
% 7.74/1.51  --bmc1_max_bound                        -1
% 7.74/1.51  --bmc1_max_bound_default                -1
% 7.74/1.51  --bmc1_symbol_reachability              true
% 7.74/1.51  --bmc1_property_lemmas                  false
% 7.74/1.51  --bmc1_k_induction                      false
% 7.74/1.51  --bmc1_non_equiv_states                 false
% 7.74/1.51  --bmc1_deadlock                         false
% 7.74/1.51  --bmc1_ucm                              false
% 7.74/1.51  --bmc1_add_unsat_core                   none
% 7.74/1.51  --bmc1_unsat_core_children              false
% 7.74/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.51  --bmc1_out_stat                         full
% 7.74/1.51  --bmc1_ground_init                      false
% 7.74/1.51  --bmc1_pre_inst_next_state              false
% 7.74/1.51  --bmc1_pre_inst_state                   false
% 7.74/1.51  --bmc1_pre_inst_reach_state             false
% 7.74/1.51  --bmc1_out_unsat_core                   false
% 7.74/1.51  --bmc1_aig_witness_out                  false
% 7.74/1.51  --bmc1_verbose                          false
% 7.74/1.51  --bmc1_dump_clauses_tptp                false
% 7.74/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.51  --bmc1_dump_file                        -
% 7.74/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.51  --bmc1_ucm_extend_mode                  1
% 7.74/1.51  --bmc1_ucm_init_mode                    2
% 7.74/1.51  --bmc1_ucm_cone_mode                    none
% 7.74/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.51  --bmc1_ucm_relax_model                  4
% 7.74/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.51  --bmc1_ucm_layered_model                none
% 7.74/1.51  --bmc1_ucm_max_lemma_size               10
% 7.74/1.51  
% 7.74/1.51  ------ AIG Options
% 7.74/1.51  
% 7.74/1.51  --aig_mode                              false
% 7.74/1.51  
% 7.74/1.51  ------ Instantiation Options
% 7.74/1.51  
% 7.74/1.51  --instantiation_flag                    true
% 7.74/1.51  --inst_sos_flag                         true
% 7.74/1.51  --inst_sos_phase                        true
% 7.74/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.51  --inst_lit_sel_side                     num_symb
% 7.74/1.51  --inst_solver_per_active                1400
% 7.74/1.51  --inst_solver_calls_frac                1.
% 7.74/1.51  --inst_passive_queue_type               priority_queues
% 7.74/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.51  --inst_passive_queues_freq              [25;2]
% 7.74/1.51  --inst_dismatching                      true
% 7.74/1.51  --inst_eager_unprocessed_to_passive     true
% 7.74/1.51  --inst_prop_sim_given                   true
% 7.74/1.51  --inst_prop_sim_new                     false
% 7.74/1.51  --inst_subs_new                         false
% 7.74/1.51  --inst_eq_res_simp                      false
% 7.74/1.51  --inst_subs_given                       false
% 7.74/1.51  --inst_orphan_elimination               true
% 7.74/1.51  --inst_learning_loop_flag               true
% 7.74/1.51  --inst_learning_start                   3000
% 7.74/1.51  --inst_learning_factor                  2
% 7.74/1.51  --inst_start_prop_sim_after_learn       3
% 7.74/1.51  --inst_sel_renew                        solver
% 7.74/1.51  --inst_lit_activity_flag                true
% 7.74/1.51  --inst_restr_to_given                   false
% 7.74/1.51  --inst_activity_threshold               500
% 7.74/1.51  --inst_out_proof                        true
% 7.74/1.51  
% 7.74/1.51  ------ Resolution Options
% 7.74/1.51  
% 7.74/1.51  --resolution_flag                       true
% 7.74/1.51  --res_lit_sel                           adaptive
% 7.74/1.51  --res_lit_sel_side                      none
% 7.74/1.51  --res_ordering                          kbo
% 7.74/1.51  --res_to_prop_solver                    active
% 7.74/1.51  --res_prop_simpl_new                    false
% 7.74/1.51  --res_prop_simpl_given                  true
% 7.74/1.51  --res_passive_queue_type                priority_queues
% 7.74/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.51  --res_passive_queues_freq               [15;5]
% 7.74/1.51  --res_forward_subs                      full
% 7.74/1.51  --res_backward_subs                     full
% 7.74/1.51  --res_forward_subs_resolution           true
% 7.74/1.51  --res_backward_subs_resolution          true
% 7.74/1.51  --res_orphan_elimination                true
% 7.74/1.51  --res_time_limit                        2.
% 7.74/1.51  --res_out_proof                         true
% 7.74/1.51  
% 7.74/1.51  ------ Superposition Options
% 7.74/1.51  
% 7.74/1.51  --superposition_flag                    true
% 7.74/1.51  --sup_passive_queue_type                priority_queues
% 7.74/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.51  --demod_completeness_check              fast
% 7.74/1.51  --demod_use_ground                      true
% 7.74/1.51  --sup_to_prop_solver                    passive
% 7.74/1.51  --sup_prop_simpl_new                    true
% 7.74/1.51  --sup_prop_simpl_given                  true
% 7.74/1.51  --sup_fun_splitting                     true
% 7.74/1.51  --sup_smt_interval                      50000
% 7.74/1.51  
% 7.74/1.51  ------ Superposition Simplification Setup
% 7.74/1.51  
% 7.74/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.51  --sup_immed_triv                        [TrivRules]
% 7.74/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_immed_bw_main                     []
% 7.74/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_input_bw                          []
% 7.74/1.51  
% 7.74/1.51  ------ Combination Options
% 7.74/1.51  
% 7.74/1.51  --comb_res_mult                         3
% 7.74/1.51  --comb_sup_mult                         2
% 7.74/1.51  --comb_inst_mult                        10
% 7.74/1.51  
% 7.74/1.51  ------ Debug Options
% 7.74/1.51  
% 7.74/1.51  --dbg_backtrace                         false
% 7.74/1.51  --dbg_dump_prop_clauses                 false
% 7.74/1.51  --dbg_dump_prop_clauses_file            -
% 7.74/1.51  --dbg_out_stat                          false
% 7.74/1.51  ------ Parsing...
% 7.74/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.51  ------ Proving...
% 7.74/1.51  ------ Problem Properties 
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  clauses                                 29
% 7.74/1.51  conjectures                             3
% 7.74/1.51  EPR                                     7
% 7.74/1.51  Horn                                    21
% 7.74/1.51  unary                                   8
% 7.74/1.51  binary                                  7
% 7.74/1.51  lits                                    68
% 7.74/1.51  lits eq                                 6
% 7.74/1.51  fd_pure                                 0
% 7.74/1.51  fd_pseudo                               0
% 7.74/1.51  fd_cond                                 0
% 7.74/1.51  fd_pseudo_cond                          2
% 7.74/1.51  AC symbols                              0
% 7.74/1.51  
% 7.74/1.51  ------ Schedule dynamic 5 is on 
% 7.74/1.51  
% 7.74/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ 
% 7.74/1.51  Current options:
% 7.74/1.51  ------ 
% 7.74/1.51  
% 7.74/1.51  ------ Input Options
% 7.74/1.51  
% 7.74/1.51  --out_options                           all
% 7.74/1.51  --tptp_safe_out                         true
% 7.74/1.51  --problem_path                          ""
% 7.74/1.51  --include_path                          ""
% 7.74/1.51  --clausifier                            res/vclausify_rel
% 7.74/1.51  --clausifier_options                    ""
% 7.74/1.51  --stdin                                 false
% 7.74/1.51  --stats_out                             all
% 7.74/1.51  
% 7.74/1.51  ------ General Options
% 7.74/1.51  
% 7.74/1.51  --fof                                   false
% 7.74/1.51  --time_out_real                         305.
% 7.74/1.51  --time_out_virtual                      -1.
% 7.74/1.51  --symbol_type_check                     false
% 7.74/1.51  --clausify_out                          false
% 7.74/1.51  --sig_cnt_out                           false
% 7.74/1.51  --trig_cnt_out                          false
% 7.74/1.51  --trig_cnt_out_tolerance                1.
% 7.74/1.51  --trig_cnt_out_sk_spl                   false
% 7.74/1.51  --abstr_cl_out                          false
% 7.74/1.51  
% 7.74/1.51  ------ Global Options
% 7.74/1.51  
% 7.74/1.51  --schedule                              default
% 7.74/1.51  --add_important_lit                     false
% 7.74/1.51  --prop_solver_per_cl                    1000
% 7.74/1.51  --min_unsat_core                        false
% 7.74/1.51  --soft_assumptions                      false
% 7.74/1.51  --soft_lemma_size                       3
% 7.74/1.51  --prop_impl_unit_size                   0
% 7.74/1.51  --prop_impl_unit                        []
% 7.74/1.51  --share_sel_clauses                     true
% 7.74/1.51  --reset_solvers                         false
% 7.74/1.51  --bc_imp_inh                            [conj_cone]
% 7.74/1.51  --conj_cone_tolerance                   3.
% 7.74/1.51  --extra_neg_conj                        none
% 7.74/1.51  --large_theory_mode                     true
% 7.74/1.51  --prolific_symb_bound                   200
% 7.74/1.51  --lt_threshold                          2000
% 7.74/1.51  --clause_weak_htbl                      true
% 7.74/1.51  --gc_record_bc_elim                     false
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing Options
% 7.74/1.51  
% 7.74/1.51  --preprocessing_flag                    true
% 7.74/1.51  --time_out_prep_mult                    0.1
% 7.74/1.51  --splitting_mode                        input
% 7.74/1.51  --splitting_grd                         true
% 7.74/1.51  --splitting_cvd                         false
% 7.74/1.51  --splitting_cvd_svl                     false
% 7.74/1.51  --splitting_nvd                         32
% 7.74/1.51  --sub_typing                            true
% 7.74/1.51  --prep_gs_sim                           true
% 7.74/1.51  --prep_unflatten                        true
% 7.74/1.51  --prep_res_sim                          true
% 7.74/1.51  --prep_upred                            true
% 7.74/1.51  --prep_sem_filter                       exhaustive
% 7.74/1.51  --prep_sem_filter_out                   false
% 7.74/1.51  --pred_elim                             true
% 7.74/1.51  --res_sim_input                         true
% 7.74/1.51  --eq_ax_congr_red                       true
% 7.74/1.51  --pure_diseq_elim                       true
% 7.74/1.51  --brand_transform                       false
% 7.74/1.51  --non_eq_to_eq                          false
% 7.74/1.51  --prep_def_merge                        true
% 7.74/1.51  --prep_def_merge_prop_impl              false
% 7.74/1.51  --prep_def_merge_mbd                    true
% 7.74/1.51  --prep_def_merge_tr_red                 false
% 7.74/1.51  --prep_def_merge_tr_cl                  false
% 7.74/1.51  --smt_preprocessing                     true
% 7.74/1.51  --smt_ac_axioms                         fast
% 7.74/1.51  --preprocessed_out                      false
% 7.74/1.51  --preprocessed_stats                    false
% 7.74/1.51  
% 7.74/1.51  ------ Abstraction refinement Options
% 7.74/1.51  
% 7.74/1.51  --abstr_ref                             []
% 7.74/1.51  --abstr_ref_prep                        false
% 7.74/1.51  --abstr_ref_until_sat                   false
% 7.74/1.51  --abstr_ref_sig_restrict                funpre
% 7.74/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.51  --abstr_ref_under                       []
% 7.74/1.51  
% 7.74/1.51  ------ SAT Options
% 7.74/1.51  
% 7.74/1.51  --sat_mode                              false
% 7.74/1.51  --sat_fm_restart_options                ""
% 7.74/1.51  --sat_gr_def                            false
% 7.74/1.51  --sat_epr_types                         true
% 7.74/1.51  --sat_non_cyclic_types                  false
% 7.74/1.51  --sat_finite_models                     false
% 7.74/1.51  --sat_fm_lemmas                         false
% 7.74/1.51  --sat_fm_prep                           false
% 7.74/1.51  --sat_fm_uc_incr                        true
% 7.74/1.51  --sat_out_model                         small
% 7.74/1.51  --sat_out_clauses                       false
% 7.74/1.51  
% 7.74/1.51  ------ QBF Options
% 7.74/1.51  
% 7.74/1.51  --qbf_mode                              false
% 7.74/1.51  --qbf_elim_univ                         false
% 7.74/1.51  --qbf_dom_inst                          none
% 7.74/1.51  --qbf_dom_pre_inst                      false
% 7.74/1.51  --qbf_sk_in                             false
% 7.74/1.51  --qbf_pred_elim                         true
% 7.74/1.51  --qbf_split                             512
% 7.74/1.51  
% 7.74/1.51  ------ BMC1 Options
% 7.74/1.51  
% 7.74/1.51  --bmc1_incremental                      false
% 7.74/1.51  --bmc1_axioms                           reachable_all
% 7.74/1.51  --bmc1_min_bound                        0
% 7.74/1.51  --bmc1_max_bound                        -1
% 7.74/1.51  --bmc1_max_bound_default                -1
% 7.74/1.51  --bmc1_symbol_reachability              true
% 7.74/1.51  --bmc1_property_lemmas                  false
% 7.74/1.51  --bmc1_k_induction                      false
% 7.74/1.51  --bmc1_non_equiv_states                 false
% 7.74/1.51  --bmc1_deadlock                         false
% 7.74/1.51  --bmc1_ucm                              false
% 7.74/1.51  --bmc1_add_unsat_core                   none
% 7.74/1.51  --bmc1_unsat_core_children              false
% 7.74/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.51  --bmc1_out_stat                         full
% 7.74/1.51  --bmc1_ground_init                      false
% 7.74/1.51  --bmc1_pre_inst_next_state              false
% 7.74/1.51  --bmc1_pre_inst_state                   false
% 7.74/1.51  --bmc1_pre_inst_reach_state             false
% 7.74/1.51  --bmc1_out_unsat_core                   false
% 7.74/1.51  --bmc1_aig_witness_out                  false
% 7.74/1.51  --bmc1_verbose                          false
% 7.74/1.51  --bmc1_dump_clauses_tptp                false
% 7.74/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.51  --bmc1_dump_file                        -
% 7.74/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.51  --bmc1_ucm_extend_mode                  1
% 7.74/1.51  --bmc1_ucm_init_mode                    2
% 7.74/1.51  --bmc1_ucm_cone_mode                    none
% 7.74/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.51  --bmc1_ucm_relax_model                  4
% 7.74/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.51  --bmc1_ucm_layered_model                none
% 7.74/1.51  --bmc1_ucm_max_lemma_size               10
% 7.74/1.51  
% 7.74/1.51  ------ AIG Options
% 7.74/1.51  
% 7.74/1.51  --aig_mode                              false
% 7.74/1.51  
% 7.74/1.51  ------ Instantiation Options
% 7.74/1.51  
% 7.74/1.51  --instantiation_flag                    true
% 7.74/1.51  --inst_sos_flag                         true
% 7.74/1.51  --inst_sos_phase                        true
% 7.74/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.51  --inst_lit_sel_side                     none
% 7.74/1.51  --inst_solver_per_active                1400
% 7.74/1.51  --inst_solver_calls_frac                1.
% 7.74/1.51  --inst_passive_queue_type               priority_queues
% 7.74/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.51  --inst_passive_queues_freq              [25;2]
% 7.74/1.51  --inst_dismatching                      true
% 7.74/1.51  --inst_eager_unprocessed_to_passive     true
% 7.74/1.51  --inst_prop_sim_given                   true
% 7.74/1.51  --inst_prop_sim_new                     false
% 7.74/1.51  --inst_subs_new                         false
% 7.74/1.51  --inst_eq_res_simp                      false
% 7.74/1.51  --inst_subs_given                       false
% 7.74/1.51  --inst_orphan_elimination               true
% 7.74/1.51  --inst_learning_loop_flag               true
% 7.74/1.51  --inst_learning_start                   3000
% 7.74/1.51  --inst_learning_factor                  2
% 7.74/1.51  --inst_start_prop_sim_after_learn       3
% 7.74/1.51  --inst_sel_renew                        solver
% 7.74/1.51  --inst_lit_activity_flag                true
% 7.74/1.51  --inst_restr_to_given                   false
% 7.74/1.51  --inst_activity_threshold               500
% 7.74/1.51  --inst_out_proof                        true
% 7.74/1.51  
% 7.74/1.51  ------ Resolution Options
% 7.74/1.51  
% 7.74/1.51  --resolution_flag                       false
% 7.74/1.51  --res_lit_sel                           adaptive
% 7.74/1.51  --res_lit_sel_side                      none
% 7.74/1.51  --res_ordering                          kbo
% 7.74/1.51  --res_to_prop_solver                    active
% 7.74/1.51  --res_prop_simpl_new                    false
% 7.74/1.51  --res_prop_simpl_given                  true
% 7.74/1.51  --res_passive_queue_type                priority_queues
% 7.74/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.51  --res_passive_queues_freq               [15;5]
% 7.74/1.51  --res_forward_subs                      full
% 7.74/1.51  --res_backward_subs                     full
% 7.74/1.51  --res_forward_subs_resolution           true
% 7.74/1.51  --res_backward_subs_resolution          true
% 7.74/1.51  --res_orphan_elimination                true
% 7.74/1.51  --res_time_limit                        2.
% 7.74/1.51  --res_out_proof                         true
% 7.74/1.51  
% 7.74/1.51  ------ Superposition Options
% 7.74/1.51  
% 7.74/1.51  --superposition_flag                    true
% 7.74/1.51  --sup_passive_queue_type                priority_queues
% 7.74/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.51  --demod_completeness_check              fast
% 7.74/1.51  --demod_use_ground                      true
% 7.74/1.51  --sup_to_prop_solver                    passive
% 7.74/1.51  --sup_prop_simpl_new                    true
% 7.74/1.51  --sup_prop_simpl_given                  true
% 7.74/1.51  --sup_fun_splitting                     true
% 7.74/1.51  --sup_smt_interval                      50000
% 7.74/1.51  
% 7.74/1.51  ------ Superposition Simplification Setup
% 7.74/1.51  
% 7.74/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.51  --sup_immed_triv                        [TrivRules]
% 7.74/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_immed_bw_main                     []
% 7.74/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.51  --sup_input_bw                          []
% 7.74/1.51  
% 7.74/1.51  ------ Combination Options
% 7.74/1.51  
% 7.74/1.51  --comb_res_mult                         3
% 7.74/1.51  --comb_sup_mult                         2
% 7.74/1.51  --comb_inst_mult                        10
% 7.74/1.51  
% 7.74/1.51  ------ Debug Options
% 7.74/1.51  
% 7.74/1.51  --dbg_backtrace                         false
% 7.74/1.51  --dbg_dump_prop_clauses                 false
% 7.74/1.51  --dbg_dump_prop_clauses_file            -
% 7.74/1.51  --dbg_out_stat                          false
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  ------ Proving...
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  % SZS status Theorem for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  fof(f12,axiom,(
% 7.74/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f19,plain,(
% 7.74/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 7.74/1.51    inference(pure_predicate_removal,[],[f12])).
% 7.74/1.51  
% 7.74/1.51  fof(f33,plain,(
% 7.74/1.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f19])).
% 7.74/1.51  
% 7.74/1.51  fof(f34,plain,(
% 7.74/1.51    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.74/1.51    inference(flattening,[],[f33])).
% 7.74/1.51  
% 7.74/1.51  fof(f75,plain,(
% 7.74/1.51    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f34])).
% 7.74/1.51  
% 7.74/1.51  fof(f16,conjecture,(
% 7.74/1.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f17,negated_conjecture,(
% 7.74/1.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.74/1.51    inference(negated_conjecture,[],[f16])).
% 7.74/1.51  
% 7.74/1.51  fof(f18,plain,(
% 7.74/1.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.74/1.51    inference(pure_predicate_removal,[],[f17])).
% 7.74/1.51  
% 7.74/1.51  fof(f40,plain,(
% 7.74/1.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f18])).
% 7.74/1.51  
% 7.74/1.51  fof(f41,plain,(
% 7.74/1.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.74/1.51    inference(flattening,[],[f40])).
% 7.74/1.51  
% 7.74/1.51  fof(f55,plain,(
% 7.74/1.51    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.74/1.51    inference(nnf_transformation,[],[f41])).
% 7.74/1.51  
% 7.74/1.51  fof(f56,plain,(
% 7.74/1.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 7.74/1.51    inference(flattening,[],[f55])).
% 7.74/1.51  
% 7.74/1.51  fof(f58,plain,(
% 7.74/1.51    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK5) | ~v1_subset_1(sK5,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK5) | v1_subset_1(sK5,u1_struct_0(X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK5,X0) & ~v1_xboole_0(sK5))) )),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f57,plain,(
% 7.74/1.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK4),X1) | ~v1_subset_1(X1,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),X1) | v1_subset_1(X1,u1_struct_0(sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(X1,sK4) & ~v1_xboole_0(X1)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f59,plain,(
% 7.74/1.51    ((r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))) & (~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v13_waybel_0(sK5,sK4) & ~v1_xboole_0(sK5)) & l1_orders_2(sK4) & v1_yellow_0(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 7.74/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f56,f58,f57])).
% 7.74/1.51  
% 7.74/1.51  fof(f90,plain,(
% 7.74/1.51    v1_yellow_0(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f86,plain,(
% 7.74/1.51    ~v2_struct_0(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f89,plain,(
% 7.74/1.51    v5_orders_2(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f91,plain,(
% 7.74/1.51    l1_orders_2(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f1,axiom,(
% 7.74/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f20,plain,(
% 7.74/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f1])).
% 7.74/1.51  
% 7.74/1.51  fof(f42,plain,(
% 7.74/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.51    inference(nnf_transformation,[],[f20])).
% 7.74/1.51  
% 7.74/1.51  fof(f43,plain,(
% 7.74/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.51    inference(rectify,[],[f42])).
% 7.74/1.51  
% 7.74/1.51  fof(f44,plain,(
% 7.74/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f45,plain,(
% 7.74/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.74/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 7.74/1.51  
% 7.74/1.51  fof(f61,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f45])).
% 7.74/1.51  
% 7.74/1.51  fof(f62,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f45])).
% 7.74/1.51  
% 7.74/1.51  fof(f7,axiom,(
% 7.74/1.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f27,plain,(
% 7.74/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.74/1.51    inference(ennf_transformation,[],[f7])).
% 7.74/1.51  
% 7.74/1.51  fof(f70,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f27])).
% 7.74/1.51  
% 7.74/1.51  fof(f5,axiom,(
% 7.74/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f48,plain,(
% 7.74/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.74/1.51    inference(nnf_transformation,[],[f5])).
% 7.74/1.51  
% 7.74/1.51  fof(f68,plain,(
% 7.74/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f48])).
% 7.74/1.51  
% 7.74/1.51  fof(f14,axiom,(
% 7.74/1.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f37,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f14])).
% 7.74/1.51  
% 7.74/1.51  fof(f38,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 7.74/1.51    inference(flattening,[],[f37])).
% 7.74/1.51  
% 7.74/1.51  fof(f82,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_yellow_0(X0,k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f38])).
% 7.74/1.51  
% 7.74/1.51  fof(f87,plain,(
% 7.74/1.51    v3_orders_2(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f88,plain,(
% 7.74/1.51    v4_orders_2(sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f9,axiom,(
% 7.74/1.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f29,plain,(
% 7.74/1.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(ennf_transformation,[],[f9])).
% 7.74/1.51  
% 7.74/1.51  fof(f72,plain,(
% 7.74/1.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f29])).
% 7.74/1.51  
% 7.74/1.51  fof(f83,plain,(
% 7.74/1.51    ( ! [X0,X1] : (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f38])).
% 7.74/1.51  
% 7.74/1.51  fof(f11,axiom,(
% 7.74/1.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f31,plain,(
% 7.74/1.51    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(ennf_transformation,[],[f11])).
% 7.74/1.51  
% 7.74/1.51  fof(f32,plain,(
% 7.74/1.51    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(flattening,[],[f31])).
% 7.74/1.51  
% 7.74/1.51  fof(f74,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f32])).
% 7.74/1.51  
% 7.74/1.51  fof(f94,plain,(
% 7.74/1.51    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f13,axiom,(
% 7.74/1.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f35,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(ennf_transformation,[],[f13])).
% 7.74/1.51  
% 7.74/1.51  fof(f36,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(flattening,[],[f35])).
% 7.74/1.51  
% 7.74/1.51  fof(f49,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(nnf_transformation,[],[f36])).
% 7.74/1.51  
% 7.74/1.51  fof(f50,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(rectify,[],[f49])).
% 7.74/1.51  
% 7.74/1.51  fof(f52,plain,(
% 7.74/1.51    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,X2,sK3(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))) )),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f51,plain,(
% 7.74/1.51    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f53,plain,(
% 7.74/1.51    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f50,f52,f51])).
% 7.74/1.51  
% 7.74/1.51  fof(f76,plain,(
% 7.74/1.51    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f53])).
% 7.74/1.51  
% 7.74/1.51  fof(f6,axiom,(
% 7.74/1.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f25,plain,(
% 7.74/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.74/1.51    inference(ennf_transformation,[],[f6])).
% 7.74/1.51  
% 7.74/1.51  fof(f26,plain,(
% 7.74/1.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.74/1.51    inference(flattening,[],[f25])).
% 7.74/1.51  
% 7.74/1.51  fof(f69,plain,(
% 7.74/1.51    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f26])).
% 7.74/1.51  
% 7.74/1.51  fof(f93,plain,(
% 7.74/1.51    v13_waybel_0(sK5,sK4)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f4,axiom,(
% 7.74/1.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f23,plain,(
% 7.74/1.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.74/1.51    inference(ennf_transformation,[],[f4])).
% 7.74/1.51  
% 7.74/1.51  fof(f24,plain,(
% 7.74/1.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.74/1.51    inference(flattening,[],[f23])).
% 7.74/1.51  
% 7.74/1.51  fof(f66,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f24])).
% 7.74/1.51  
% 7.74/1.51  fof(f92,plain,(
% 7.74/1.51    ~v1_xboole_0(sK5)),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f15,axiom,(
% 7.74/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f39,plain,(
% 7.74/1.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f15])).
% 7.74/1.51  
% 7.74/1.51  fof(f54,plain,(
% 7.74/1.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.51    inference(nnf_transformation,[],[f39])).
% 7.74/1.51  
% 7.74/1.51  fof(f85,plain,(
% 7.74/1.51    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f54])).
% 7.74/1.51  
% 7.74/1.51  fof(f96,plain,(
% 7.74/1.51    r2_hidden(k3_yellow_0(sK4),sK5) | ~v1_subset_1(sK5,u1_struct_0(sK4))),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f67,plain,(
% 7.74/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f48])).
% 7.74/1.51  
% 7.74/1.51  fof(f60,plain,(
% 7.74/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f45])).
% 7.74/1.51  
% 7.74/1.51  fof(f10,axiom,(
% 7.74/1.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f30,plain,(
% 7.74/1.51    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(ennf_transformation,[],[f10])).
% 7.74/1.51  
% 7.74/1.51  fof(f73,plain,(
% 7.74/1.51    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f30])).
% 7.74/1.51  
% 7.74/1.51  fof(f2,axiom,(
% 7.74/1.51    v1_xboole_0(k1_xboole_0)),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f63,plain,(
% 7.74/1.51    v1_xboole_0(k1_xboole_0)),
% 7.74/1.51    inference(cnf_transformation,[],[f2])).
% 7.74/1.51  
% 7.74/1.51  fof(f84,plain,(
% 7.74/1.51    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f54])).
% 7.74/1.51  
% 7.74/1.51  fof(f97,plain,(
% 7.74/1.51    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 7.74/1.51    inference(equality_resolution,[],[f84])).
% 7.74/1.51  
% 7.74/1.51  fof(f95,plain,(
% 7.74/1.51    ~r2_hidden(k3_yellow_0(sK4),sK5) | v1_subset_1(sK5,u1_struct_0(sK4))),
% 7.74/1.51    inference(cnf_transformation,[],[f59])).
% 7.74/1.51  
% 7.74/1.51  fof(f3,axiom,(
% 7.74/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f21,plain,(
% 7.74/1.51    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.51    inference(ennf_transformation,[],[f3])).
% 7.74/1.51  
% 7.74/1.51  fof(f22,plain,(
% 7.74/1.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.51    inference(flattening,[],[f21])).
% 7.74/1.51  
% 7.74/1.51  fof(f46,plain,(
% 7.74/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 7.74/1.51    introduced(choice_axiom,[])).
% 7.74/1.51  
% 7.74/1.51  fof(f47,plain,(
% 7.74/1.51    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.74/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f46])).
% 7.74/1.51  
% 7.74/1.51  fof(f64,plain,(
% 7.74/1.51    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f47])).
% 7.74/1.51  
% 7.74/1.51  fof(f8,axiom,(
% 7.74/1.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 7.74/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.51  
% 7.74/1.51  fof(f28,plain,(
% 7.74/1.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 7.74/1.51    inference(ennf_transformation,[],[f8])).
% 7.74/1.51  
% 7.74/1.51  fof(f71,plain,(
% 7.74/1.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 7.74/1.51    inference(cnf_transformation,[],[f28])).
% 7.74/1.51  
% 7.74/1.51  fof(f65,plain,(
% 7.74/1.51    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.74/1.51    inference(cnf_transformation,[],[f47])).
% 7.74/1.51  
% 7.74/1.51  cnf(c_15,plain,
% 7.74/1.51      ( r1_yellow_0(X0,k1_xboole_0)
% 7.74/1.51      | v2_struct_0(X0)
% 7.74/1.51      | ~ v5_orders_2(X0)
% 7.74/1.51      | ~ v1_yellow_0(X0)
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_32,negated_conjecture,
% 7.74/1.51      ( v1_yellow_0(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_507,plain,
% 7.74/1.51      ( r1_yellow_0(X0,k1_xboole_0)
% 7.74/1.51      | v2_struct_0(X0)
% 7.74/1.51      | ~ v5_orders_2(X0)
% 7.74/1.51      | ~ l1_orders_2(X0)
% 7.74/1.51      | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_508,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k1_xboole_0)
% 7.74/1.51      | v2_struct_0(sK4)
% 7.74/1.51      | ~ v5_orders_2(sK4)
% 7.74/1.51      | ~ l1_orders_2(sK4) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_507]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_36,negated_conjecture,
% 7.74/1.51      ( ~ v2_struct_0(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_33,negated_conjecture,
% 7.74/1.51      ( v5_orders_2(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_31,negated_conjecture,
% 7.74/1.51      ( l1_orders_2(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_77,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k1_xboole_0)
% 7.74/1.51      | v2_struct_0(sK4)
% 7.74/1.51      | ~ v5_orders_2(sK4)
% 7.74/1.51      | ~ v1_yellow_0(sK4)
% 7.74/1.51      | ~ l1_orders_2(sK4) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_510,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k1_xboole_0) ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_508,c_36,c_33,c_32,c_31,c_77]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3201,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k1_xboole_0) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_1,plain,
% 7.74/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3214,plain,
% 7.74/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_0,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3215,plain,
% 7.74/1.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4602,plain,
% 7.74/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3214,c_3215]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_10,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.51      | ~ r2_hidden(X2,X0)
% 7.74/1.51      | ~ v1_xboole_0(X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7,plain,
% 7.74/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_280,plain,
% 7.74/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.74/1.51      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_281,plain,
% 7.74/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_280]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_364,plain,
% 7.74/1.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 7.74/1.51      inference(bin_hyper_res,[status(thm)],[c_10,c_281]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3202,plain,
% 7.74/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.51      | r1_tarski(X1,X2) != iProver_top
% 7.74/1.51      | v1_xboole_0(X2) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6478,plain,
% 7.74/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4602,c_3202]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16631,plain,
% 7.74/1.51      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3214,c_6478]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_23,plain,
% 7.74/1.51      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.74/1.51      | ~ v3_orders_2(X0)
% 7.74/1.51      | ~ v4_orders_2(X0)
% 7.74/1.51      | v2_struct_0(X0)
% 7.74/1.51      | ~ v5_orders_2(X0)
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_610,plain,
% 7.74/1.51      ( r1_yellow_0(X0,k5_waybel_0(X0,X1))
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.74/1.51      | ~ v3_orders_2(X0)
% 7.74/1.51      | ~ v4_orders_2(X0)
% 7.74/1.51      | v2_struct_0(X0)
% 7.74/1.51      | ~ l1_orders_2(X0)
% 7.74/1.51      | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_611,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0))
% 7.74/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.74/1.51      | ~ v3_orders_2(sK4)
% 7.74/1.51      | ~ v4_orders_2(sK4)
% 7.74/1.51      | v2_struct_0(sK4)
% 7.74/1.51      | ~ l1_orders_2(sK4) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_610]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_35,negated_conjecture,
% 7.74/1.51      ( v3_orders_2(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_34,negated_conjecture,
% 7.74/1.51      ( v4_orders_2(sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_615,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0))
% 7.74/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_611,c_36,c_35,c_34,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3199,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = iProver_top
% 7.74/1.51      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_12,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_795,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_796,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_795]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3193,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_22,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.74/1.51      | ~ v3_orders_2(X1)
% 7.74/1.51      | ~ v4_orders_2(X1)
% 7.74/1.51      | v2_struct_0(X1)
% 7.74/1.51      | ~ v5_orders_2(X1)
% 7.74/1.51      | ~ l1_orders_2(X1)
% 7.74/1.51      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0 ),
% 7.74/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_628,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 7.74/1.51      | ~ v3_orders_2(X1)
% 7.74/1.51      | ~ v4_orders_2(X1)
% 7.74/1.51      | v2_struct_0(X1)
% 7.74/1.51      | ~ l1_orders_2(X1)
% 7.74/1.51      | k1_yellow_0(X1,k5_waybel_0(X1,X0)) = X0
% 7.74/1.51      | sK4 != X1 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_629,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.74/1.51      | ~ v3_orders_2(sK4)
% 7.74/1.51      | ~ v4_orders_2(sK4)
% 7.74/1.51      | v2_struct_0(sK4)
% 7.74/1.51      | ~ l1_orders_2(sK4)
% 7.74/1.51      | k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0 ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_628]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_633,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.74/1.51      | k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0 ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_629,c_36,c_35,c_34,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3198,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k5_waybel_0(sK4,X0)) = X0
% 7.74/1.51      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3601,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X0))) = k1_yellow_0(sK4,X0) ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3193,c_3198]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_14,plain,
% 7.74/1.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 7.74/1.51      | ~ r1_yellow_0(X0,X2)
% 7.74/1.51      | ~ r1_yellow_0(X0,X1)
% 7.74/1.51      | ~ r1_tarski(X1,X2)
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_770,plain,
% 7.74/1.51      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
% 7.74/1.51      | ~ r1_yellow_0(X0,X1)
% 7.74/1.51      | ~ r1_yellow_0(X0,X2)
% 7.74/1.51      | ~ r1_tarski(X1,X2)
% 7.74/1.51      | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_771,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1))
% 7.74/1.51      | ~ r1_yellow_0(sK4,X1)
% 7.74/1.51      | ~ r1_yellow_0(sK4,X0)
% 7.74/1.51      | ~ r1_tarski(X0,X1) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_770]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3195,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X1) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5084,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k1_yellow_0(sK4,X1)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3601,c_3195]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_28,negated_conjecture,
% 7.74/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 7.74/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3207,plain,
% 7.74/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_21,plain,
% 7.74/1.51      ( ~ r1_orders_2(X0,X1,X2)
% 7.74/1.51      | ~ v13_waybel_0(X3,X0)
% 7.74/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.74/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.74/1.51      | ~ r2_hidden(X1,X3)
% 7.74/1.51      | r2_hidden(X2,X3)
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_730,plain,
% 7.74/1.51      ( ~ r1_orders_2(X0,X1,X2)
% 7.74/1.51      | ~ v13_waybel_0(X3,X0)
% 7.74/1.51      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.74/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.74/1.51      | ~ r2_hidden(X1,X3)
% 7.74/1.51      | r2_hidden(X2,X3)
% 7.74/1.51      | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_731,plain,
% 7.74/1.51      ( ~ r1_orders_2(sK4,X0,X1)
% 7.74/1.51      | ~ v13_waybel_0(X2,sK4)
% 7.74/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.74/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r2_hidden(X0,X2)
% 7.74/1.51      | r2_hidden(X1,X2) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_730]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_9,plain,
% 7.74/1.51      ( m1_subset_1(X0,X1)
% 7.74/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.74/1.51      | ~ r2_hidden(X0,X2) ),
% 7.74/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_747,plain,
% 7.74/1.51      ( ~ r1_orders_2(sK4,X0,X1)
% 7.74/1.51      | ~ v13_waybel_0(X2,sK4)
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.74/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r2_hidden(X0,X2)
% 7.74/1.51      | r2_hidden(X1,X2) ),
% 7.74/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_731,c_9]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3197,plain,
% 7.74/1.51      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.74/1.51      | v13_waybel_0(X2,sK4) != iProver_top
% 7.74/1.51      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.74/1.51      | r2_hidden(X0,X2) != iProver_top
% 7.74/1.51      | r2_hidden(X1,X2) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5165,plain,
% 7.74/1.51      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.74/1.51      | v13_waybel_0(sK5,sK4) != iProver_top
% 7.74/1.51      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(X0,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(X1,sK5) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3207,c_3197]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_45,plain,
% 7.74/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_29,negated_conjecture,
% 7.74/1.51      ( v13_waybel_0(sK5,sK4) ),
% 7.74/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_972,plain,
% 7.74/1.51      ( ~ r1_orders_2(sK4,X0,X1)
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.74/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r2_hidden(X0,X2)
% 7.74/1.51      | r2_hidden(X1,X2)
% 7.74/1.51      | sK5 != X2
% 7.74/1.51      | sK4 != sK4 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_29,c_747]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_973,plain,
% 7.74/1.51      ( ~ r1_orders_2(sK4,X0,X1)
% 7.74/1.51      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 7.74/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r2_hidden(X0,sK5)
% 7.74/1.51      | r2_hidden(X1,sK5) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_972]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_974,plain,
% 7.74/1.51      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.74/1.51      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.74/1.51      | r2_hidden(X0,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(X1,sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5244,plain,
% 7.74/1.51      ( r1_orders_2(sK4,X0,X1) != iProver_top
% 7.74/1.51      | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(X0,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(X1,sK5) = iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_5165,c_45,c_974]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5745,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_5084,c_5244]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6345,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k1_yellow_0(sK4,X1))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3199,c_5745]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16779,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_16631,c_6345]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3625,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(X0,sK5),sK5) | r1_tarski(X0,sK5) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4422,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(sK5,sK5),sK5) | r1_tarski(sK5,sK5) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3625]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4425,plain,
% 7.74/1.51      ( r2_hidden(sK0(sK5,sK5),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_4422]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3626,plain,
% 7.74/1.51      ( r2_hidden(sK0(X0,sK5),X0) | r1_tarski(X0,sK5) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4420,plain,
% 7.74/1.51      ( r2_hidden(sK0(sK5,sK5),sK5) | r1_tarski(sK5,sK5) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3626]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4429,plain,
% 7.74/1.51      ( r2_hidden(sK0(sK5,sK5),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(sK5,sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_4420]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3211,plain,
% 7.74/1.51      ( m1_subset_1(X0,X1) != iProver_top
% 7.74/1.51      | r2_hidden(X0,X1) = iProver_top
% 7.74/1.51      | v1_xboole_0(X1) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4610,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top
% 7.74/1.51      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3193,c_3211]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_30,negated_conjecture,
% 7.74/1.51      ( ~ v1_xboole_0(sK5) ),
% 7.74/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_43,plain,
% 7.74/1.51      ( v1_xboole_0(sK5) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_24,plain,
% 7.74/1.51      ( v1_subset_1(X0,X1)
% 7.74/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.51      | X0 = X1 ),
% 7.74/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_365,plain,
% 7.74/1.51      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 7.74/1.51      inference(bin_hyper_res,[status(thm)],[c_24,c_281]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_26,negated_conjecture,
% 7.74/1.51      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.74/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_284,plain,
% 7.74/1.51      ( ~ v1_subset_1(sK5,u1_struct_0(sK4))
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.74/1.51      inference(prop_impl,[status(thm)],[c_26]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_576,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | ~ r1_tarski(X0,X1)
% 7.74/1.51      | X1 = X0
% 7.74/1.51      | u1_struct_0(sK4) != X1
% 7.74/1.51      | sK5 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_365,c_284]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_577,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.74/1.51      | u1_struct_0(sK4) = sK5 ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_576]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_578,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_797,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3418,plain,
% 7.74/1.51      ( ~ m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
% 7.74/1.51      | v1_xboole_0(u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3419,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top
% 7.74/1.51      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3418]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_2527,plain,
% 7.74/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.74/1.51      theory(equality) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3259,plain,
% 7.74/1.51      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2527]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3560,plain,
% 7.74/1.51      ( ~ v1_xboole_0(u1_struct_0(sK4))
% 7.74/1.51      | v1_xboole_0(sK5)
% 7.74/1.51      | sK5 != u1_struct_0(sK4) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3259]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3561,plain,
% 7.74/1.51      ( sK5 != u1_struct_0(sK4)
% 7.74/1.51      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | v1_xboole_0(sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3560]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_8,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.74/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3209,plain,
% 7.74/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3747,plain,
% 7.74/1.51      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3207,c_3209]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3567,plain,
% 7.74/1.51      ( ~ r2_hidden(X0,X1)
% 7.74/1.51      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 7.74/1.51      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_364]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4342,plain,
% 7.74/1.51      ( ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.74/1.51      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3567]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4343,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_4342]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_2524,plain,( X0 = X0 ),theory(equality) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4636,plain,
% 7.74/1.51      ( sK5 = sK5 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2524]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_2525,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3653,plain,
% 7.74/1.51      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2525]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4640,plain,
% 7.74/1.51      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3653]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5233,plain,
% 7.74/1.51      ( u1_struct_0(sK4) != sK5 | sK5 = u1_struct_0(sK4) | sK5 != sK5 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_4640]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5861,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_4610,c_43,c_578,c_797,c_3419,c_3561,c_3747,c_4343,
% 7.74/1.51                 c_4636,c_5233]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3210,plain,
% 7.74/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3208,plain,
% 7.74/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.74/1.51      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.74/1.51      | r2_hidden(X0,X2) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4712,plain,
% 7.74/1.51      ( m1_subset_1(X0,X1) = iProver_top
% 7.74/1.51      | r2_hidden(X0,X2) != iProver_top
% 7.74/1.51      | r1_tarski(X2,X1) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3210,c_3208]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6691,plain,
% 7.74/1.51      ( m1_subset_1(k1_yellow_0(sK4,X0),X1) = iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_5861,c_4712]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_9516,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),X1) != iProver_top
% 7.74/1.51      | v1_xboole_0(X1) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_6691,c_3211]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_2,plain,
% 7.74/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.74/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7588,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),X1)
% 7.74/1.51      | ~ r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4))
% 7.74/1.51      | ~ r1_tarski(u1_struct_0(sK4),X1) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7590,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_7588]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_9877,plain,
% 7.74/1.51      ( r1_tarski(u1_struct_0(sK4),X1) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_9516,c_43,c_578,c_797,c_3419,c_3561,c_3747,c_4343,
% 7.74/1.51                 c_4636,c_5233,c_7590]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_9878,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),X1) = iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),X1) != iProver_top ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_9877]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 7.74/1.51      | ~ l1_orders_2(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_788,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_789,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_788]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3194,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3600,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) = k3_yellow_0(sK4) ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3194,c_3198]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5072,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3600,c_3195]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_42,plain,
% 7.74/1.51      ( l1_orders_2(sK4) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_82,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 7.74/1.51      | l1_orders_2(X0) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_84,plain,
% 7.74/1.51      ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
% 7.74/1.51      | l1_orders_2(sK4) != iProver_top ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_82]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3267,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)))
% 7.74/1.51      | ~ m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_615]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3268,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4))) = iProver_top
% 7.74/1.51      | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3267]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5459,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_5072,c_42,c_84,c_3268]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5460,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k1_yellow_0(sK4,X0),k3_yellow_0(sK4)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_5459]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5468,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_5460,c_5244]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6186,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X0,k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_5468,c_42,c_84]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16778,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_16631,c_6186]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3,plain,
% 7.74/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_112,plain,
% 7.74/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_25,plain,
% 7.74/1.51      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 7.74/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_27,negated_conjecture,
% 7.74/1.51      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 7.74/1.51      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.74/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_282,plain,
% 7.74/1.51      ( v1_subset_1(sK5,u1_struct_0(sK4))
% 7.74/1.51      | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
% 7.74/1.51      inference(prop_impl,[status(thm)],[c_27]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_589,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 7.74/1.51      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | u1_struct_0(sK4) != X0
% 7.74/1.51      | sK5 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_25,c_282]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_590,plain,
% 7.74/1.51      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | sK5 != u1_struct_0(sK4) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_589]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_591,plain,
% 7.74/1.51      ( sK5 != u1_struct_0(sK4)
% 7.74/1.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_2529,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.74/1.51      theory(equality) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3721,plain,
% 7.74/1.51      ( m1_subset_1(X0,X1)
% 7.74/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | X1 != k1_zfmisc_1(u1_struct_0(sK4))
% 7.74/1.51      | X0 != sK5 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2529]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4228,plain,
% 7.74/1.51      ( m1_subset_1(u1_struct_0(sK4),X0)
% 7.74/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | X0 != k1_zfmisc_1(u1_struct_0(sK4))
% 7.74/1.51      | u1_struct_0(sK4) != sK5 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3721]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5002,plain,
% 7.74/1.51      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | u1_struct_0(sK4) != sK5
% 7.74/1.51      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_4228]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5003,plain,
% 7.74/1.51      ( u1_struct_0(sK4) != sK5
% 7.74/1.51      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 7.74/1.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.74/1.51      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_5002]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5588,plain,
% 7.74/1.51      ( k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_2524]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.51      | m1_subset_1(sK1(X1,X0),X1)
% 7.74/1.51      | X0 = X1 ),
% 7.74/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_361,plain,
% 7.74/1.51      ( m1_subset_1(sK1(X0,X1),X0) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.74/1.51      inference(bin_hyper_res,[status(thm)],[c_5,c_281]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3203,plain,
% 7.74/1.51      ( X0 = X1
% 7.74/1.51      | m1_subset_1(sK1(X1,X0),X1) = iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6007,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),X0))) = sK1(u1_struct_0(sK4),X0)
% 7.74/1.51      | u1_struct_0(sK4) = X0
% 7.74/1.51      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3203,c_3198]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7542,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) = sK1(u1_struct_0(sK4),sK5)
% 7.74/1.51      | u1_struct_0(sK4) = sK5 ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3747,c_6007]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_11,plain,
% 7.74/1.51      ( ~ l1_orders_2(X0)
% 7.74/1.51      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 7.74/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_804,plain,
% 7.74/1.51      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK4 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_805,plain,
% 7.74/1.51      ( k1_yellow_0(sK4,k1_xboole_0) = k3_yellow_0(sK4) ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_804]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4152,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,k1_xboole_0) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_805,c_3195]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_37,plain,
% 7.74/1.51      ( v2_struct_0(sK4) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_40,plain,
% 7.74/1.51      ( v5_orders_2(sK4) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_41,plain,
% 7.74/1.51      ( v1_yellow_0(sK4) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_76,plain,
% 7.74/1.51      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 7.74/1.51      | v2_struct_0(X0) = iProver_top
% 7.74/1.51      | v5_orders_2(X0) != iProver_top
% 7.74/1.51      | v1_yellow_0(X0) != iProver_top
% 7.74/1.51      | l1_orders_2(X0) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_78,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,k1_xboole_0) = iProver_top
% 7.74/1.51      | v2_struct_0(sK4) = iProver_top
% 7.74/1.51      | v5_orders_2(sK4) != iProver_top
% 7.74/1.51      | v1_yellow_0(sK4) != iProver_top
% 7.74/1.51      | l1_orders_2(sK4) != iProver_top ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_76]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4161,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_4152,c_37,c_40,c_41,c_42,c_78]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4162,plain,
% 7.74/1.51      ( r1_orders_2(sK4,k3_yellow_0(sK4),k1_yellow_0(sK4,X0)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_4161]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7873,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r1_orders_2(sK4,k3_yellow_0(sK4),sK1(u1_struct_0(sK4),sK5)) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_7542,c_4162]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.51      | ~ r2_hidden(sK1(X1,X0),X0)
% 7.74/1.51      | X0 = X1 ),
% 7.74/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_360,plain,
% 7.74/1.51      ( ~ r2_hidden(sK1(X0,X1),X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.74/1.51      inference(bin_hyper_res,[status(thm)],[c_4,c_281]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3640,plain,
% 7.74/1.51      ( ~ r2_hidden(sK1(X0,sK5),sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_360]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4407,plain,
% 7.74/1.51      ( ~ r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5)
% 7.74/1.51      | ~ r1_tarski(sK5,u1_struct_0(sK4))
% 7.74/1.51      | sK5 = u1_struct_0(sK4) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3640]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4411,plain,
% 7.74/1.51      ( sK5 = u1_struct_0(sK4)
% 7.74/1.51      | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_4407]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3200,plain,
% 7.74/1.51      ( sK5 != u1_struct_0(sK4)
% 7.74/1.51      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3296,plain,
% 7.74/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3704,plain,
% 7.74/1.51      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3296]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3705,plain,
% 7.74/1.51      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3704]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3397,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 7.74/1.51      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3817,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3397]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3820,plain,
% 7.74/1.51      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3817]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3398,plain,
% 7.74/1.51      ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
% 7.74/1.51      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3815,plain,
% 7.74/1.51      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3398]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3824,plain,
% 7.74/1.51      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3815]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5755,plain,
% 7.74/1.51      ( sK5 != u1_struct_0(sK4)
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_3200,c_591,c_3705,c_3820,c_3824]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5251,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,X0),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_4162,c_5244]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6084,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_5251,c_797]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7863,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
% 7.74/1.51      | r2_hidden(sK1(u1_struct_0(sK4),sK5),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_7542,c_6084]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_8142,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r1_yellow_0(sK4,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_7873,c_578,c_3747,c_4411,c_5755,c_7863]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_8146,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3199,c_8142]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_7875,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | m1_subset_1(sK1(u1_struct_0(sK4),sK5),u1_struct_0(sK4)) = iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_7542,c_3193]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_8475,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r1_tarski(k1_xboole_0,k5_waybel_0(sK4,sK1(u1_struct_0(sK4),sK5))) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_8146,c_7875]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16801,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_16631,c_8475]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17252,plain,
% 7.74/1.51      ( r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_16778,c_112,c_591,c_3705,c_3820,c_3824,c_4636,c_5233,
% 7.74/1.51                 c_16801]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17253,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_17252]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17259,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_tarski(u1_struct_0(sK4),sK5) != iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_9878,c_17253]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_278,plain,
% 7.74/1.51      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.74/1.51      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_279,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_278]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_1292,plain,
% 7.74/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | u1_struct_0(sK4) != X1
% 7.74/1.51      | u1_struct_0(sK4) = sK5
% 7.74/1.51      | sK5 != X0 ),
% 7.74/1.51      inference(resolution_lifted,[status(thm)],[c_279,c_577]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_1293,plain,
% 7.74/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5)
% 7.74/1.51      | u1_struct_0(sK4) = sK5 ),
% 7.74/1.51      inference(unflattening,[status(thm)],[c_1292]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_1295,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5) | u1_struct_0(sK4) = sK5 ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_1293,c_28]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3188,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_1295]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_5249,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X1) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,X1),u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X1),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3195,c_5244]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6280,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X1) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X1),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
% 7.74/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3193,c_5249]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6337,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,X1) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,X0),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_6084,c_6280]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13375,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3747,c_6337]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3573,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.74/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3577,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3573]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3572,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 7.74/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3579,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_3572]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_4169,plain,
% 7.74/1.51      ( ~ r2_hidden(X0,k1_xboole_0)
% 7.74/1.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.74/1.51      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_364]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6330,plain,
% 7.74/1.51      ( ~ r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 7.74/1.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.74/1.51      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_4169]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6332,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) != iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.74/1.51      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_6330]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6331,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0)
% 7.74/1.51      | r1_tarski(k1_xboole_0,sK5) ),
% 7.74/1.51      inference(instantiation,[status(thm)],[c_3626]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_6334,plain,
% 7.74/1.51      ( r2_hidden(sK0(k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 7.74/1.51      | r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_6331]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13400,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_13375,c_112,c_3577,c_3579,c_6332,c_6334]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13401,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k1_yellow_0(sK4,u1_struct_0(sK4)),sK5) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.74/1.51      inference(renaming,[status(thm)],[c_13400]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13404,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | m1_subset_1(k1_yellow_0(sK4,u1_struct_0(sK4)),X0) = iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,X0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_13401,c_4712]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13483,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(k1_yellow_0(sK4,u1_struct_0(sK4)),X0) = iProver_top
% 7.74/1.51      | r1_tarski(sK5,k1_zfmisc_1(X0)) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_13404,c_3209]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_3213,plain,
% 7.74/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.74/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.74/1.51      | r1_tarski(X1,X2) != iProver_top ),
% 7.74/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_13770,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,u1_struct_0(sK4)) != iProver_top
% 7.74/1.51      | r1_yellow_0(sK4,sK5) != iProver_top
% 7.74/1.51      | r2_hidden(X0,X1) = iProver_top
% 7.74/1.51      | r2_hidden(X0,k1_yellow_0(sK4,u1_struct_0(sK4))) != iProver_top
% 7.74/1.51      | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,k1_zfmisc_1(X1)) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_13483,c_3213]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16881,plain,
% 7.74/1.51      ( r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_13770,c_112,c_591,c_3705,c_3820,c_3824,c_4636,c_5233,
% 7.74/1.51                 c_16801]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_16885,plain,
% 7.74/1.51      ( u1_struct_0(sK4) = sK5 ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3188,c_16881]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17264,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | r1_tarski(sK5,sK5) != iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(light_normalisation,[status(thm)],[c_17259,c_16885]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17610,plain,
% 7.74/1.51      ( r1_yellow_0(sK4,X0) != iProver_top
% 7.74/1.51      | v1_xboole_0(X0) != iProver_top ),
% 7.74/1.51      inference(global_propositional_subsumption,
% 7.74/1.51                [status(thm)],
% 7.74/1.51                [c_16779,c_4425,c_4429,c_17264]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(c_17616,plain,
% 7.74/1.51      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.74/1.51      inference(superposition,[status(thm)],[c_3201,c_17610]) ).
% 7.74/1.51  
% 7.74/1.51  cnf(contradiction,plain,
% 7.74/1.51      ( $false ),
% 7.74/1.51      inference(minisat,[status(thm)],[c_17616,c_112]) ).
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.51  
% 7.74/1.51  ------                               Statistics
% 7.74/1.51  
% 7.74/1.51  ------ General
% 7.74/1.51  
% 7.74/1.51  abstr_ref_over_cycles:                  0
% 7.74/1.51  abstr_ref_under_cycles:                 0
% 7.74/1.51  gc_basic_clause_elim:                   0
% 7.74/1.51  forced_gc_time:                         0
% 7.74/1.51  parsing_time:                           0.01
% 7.74/1.51  unif_index_cands_time:                  0.
% 7.74/1.51  unif_index_add_time:                    0.
% 7.74/1.51  orderings_time:                         0.
% 7.74/1.51  out_proof_time:                         0.024
% 7.74/1.51  total_time:                             0.789
% 7.74/1.51  num_of_symbols:                         57
% 7.74/1.51  num_of_terms:                           15812
% 7.74/1.51  
% 7.74/1.51  ------ Preprocessing
% 7.74/1.51  
% 7.74/1.51  num_of_splits:                          0
% 7.74/1.51  num_of_split_atoms:                     0
% 7.74/1.51  num_of_reused_defs:                     0
% 7.74/1.51  num_eq_ax_congr_red:                    33
% 7.74/1.51  num_of_sem_filtered_clauses:            1
% 7.74/1.51  num_of_subtypes:                        0
% 7.74/1.51  monotx_restored_types:                  0
% 7.74/1.51  sat_num_of_epr_types:                   0
% 7.74/1.51  sat_num_of_non_cyclic_types:            0
% 7.74/1.51  sat_guarded_non_collapsed_types:        0
% 7.74/1.51  num_pure_diseq_elim:                    0
% 7.74/1.51  simp_replaced_by:                       0
% 7.74/1.51  res_preprocessed:                       155
% 7.74/1.51  prep_upred:                             0
% 7.74/1.51  prep_unflattend:                        128
% 7.74/1.51  smt_new_axioms:                         0
% 7.74/1.51  pred_elim_cands:                        7
% 7.74/1.51  pred_elim:                              7
% 7.74/1.51  pred_elim_cl:                           8
% 7.74/1.51  pred_elim_cycles:                       17
% 7.74/1.51  merged_defs:                            10
% 7.74/1.51  merged_defs_ncl:                        0
% 7.74/1.51  bin_hyper_res:                          14
% 7.74/1.51  prep_cycles:                            4
% 7.74/1.51  pred_elim_time:                         0.029
% 7.74/1.51  splitting_time:                         0.
% 7.74/1.51  sem_filter_time:                        0.
% 7.74/1.51  monotx_time:                            0.001
% 7.74/1.51  subtype_inf_time:                       0.
% 7.74/1.51  
% 7.74/1.51  ------ Problem properties
% 7.74/1.51  
% 7.74/1.51  clauses:                                29
% 7.74/1.51  conjectures:                            3
% 7.74/1.51  epr:                                    7
% 7.74/1.51  horn:                                   21
% 7.74/1.51  ground:                                 9
% 7.74/1.51  unary:                                  8
% 7.74/1.51  binary:                                 7
% 7.74/1.51  lits:                                   68
% 7.74/1.51  lits_eq:                                6
% 7.74/1.51  fd_pure:                                0
% 7.74/1.51  fd_pseudo:                              0
% 7.74/1.51  fd_cond:                                0
% 7.74/1.51  fd_pseudo_cond:                         2
% 7.74/1.51  ac_symbols:                             0
% 7.74/1.51  
% 7.74/1.51  ------ Propositional Solver
% 7.74/1.51  
% 7.74/1.51  prop_solver_calls:                      28
% 7.74/1.51  prop_fast_solver_calls:                 2273
% 7.74/1.51  smt_solver_calls:                       0
% 7.74/1.51  smt_fast_solver_calls:                  0
% 7.74/1.51  prop_num_of_clauses:                    7294
% 7.74/1.51  prop_preprocess_simplified:             15793
% 7.74/1.51  prop_fo_subsumed:                       126
% 7.74/1.51  prop_solver_time:                       0.
% 7.74/1.51  smt_solver_time:                        0.
% 7.74/1.51  smt_fast_solver_time:                   0.
% 7.74/1.51  prop_fast_solver_time:                  0.
% 7.74/1.51  prop_unsat_core_time:                   0.
% 7.74/1.51  
% 7.74/1.51  ------ QBF
% 7.74/1.51  
% 7.74/1.51  qbf_q_res:                              0
% 7.74/1.51  qbf_num_tautologies:                    0
% 7.74/1.51  qbf_prep_cycles:                        0
% 7.74/1.51  
% 7.74/1.51  ------ BMC1
% 7.74/1.51  
% 7.74/1.51  bmc1_current_bound:                     -1
% 7.74/1.51  bmc1_last_solved_bound:                 -1
% 7.74/1.51  bmc1_unsat_core_size:                   -1
% 7.74/1.51  bmc1_unsat_core_parents_size:           -1
% 7.74/1.51  bmc1_merge_next_fun:                    0
% 7.74/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.51  
% 7.74/1.51  ------ Instantiation
% 7.74/1.51  
% 7.74/1.51  inst_num_of_clauses:                    1779
% 7.74/1.51  inst_num_in_passive:                    533
% 7.74/1.51  inst_num_in_active:                     666
% 7.74/1.51  inst_num_in_unprocessed:                580
% 7.74/1.51  inst_num_of_loops:                      1020
% 7.74/1.51  inst_num_of_learning_restarts:          0
% 7.74/1.51  inst_num_moves_active_passive:          353
% 7.74/1.51  inst_lit_activity:                      0
% 7.74/1.51  inst_lit_activity_moves:                0
% 7.74/1.51  inst_num_tautologies:                   0
% 7.74/1.51  inst_num_prop_implied:                  0
% 7.74/1.51  inst_num_existing_simplified:           0
% 7.74/1.51  inst_num_eq_res_simplified:             0
% 7.74/1.51  inst_num_child_elim:                    0
% 7.74/1.51  inst_num_of_dismatching_blockings:      1015
% 7.74/1.51  inst_num_of_non_proper_insts:           2105
% 7.74/1.51  inst_num_of_duplicates:                 0
% 7.74/1.51  inst_inst_num_from_inst_to_res:         0
% 7.74/1.51  inst_dismatching_checking_time:         0.
% 7.74/1.51  
% 7.74/1.51  ------ Resolution
% 7.74/1.51  
% 7.74/1.51  res_num_of_clauses:                     0
% 7.74/1.51  res_num_in_passive:                     0
% 7.74/1.51  res_num_in_active:                      0
% 7.74/1.51  res_num_of_loops:                       159
% 7.74/1.51  res_forward_subset_subsumed:            93
% 7.74/1.51  res_backward_subset_subsumed:           0
% 7.74/1.51  res_forward_subsumed:                   0
% 7.74/1.51  res_backward_subsumed:                  1
% 7.74/1.51  res_forward_subsumption_resolution:     8
% 7.74/1.51  res_backward_subsumption_resolution:    0
% 7.74/1.51  res_clause_to_clause_subsumption:       3916
% 7.74/1.51  res_orphan_elimination:                 0
% 7.74/1.51  res_tautology_del:                      131
% 7.74/1.51  res_num_eq_res_simplified:              0
% 7.74/1.51  res_num_sel_changes:                    0
% 7.74/1.51  res_moves_from_active_to_pass:          0
% 7.74/1.51  
% 7.74/1.51  ------ Superposition
% 7.74/1.51  
% 7.74/1.51  sup_time_total:                         0.
% 7.74/1.51  sup_time_generating:                    0.
% 7.74/1.51  sup_time_sim_full:                      0.
% 7.74/1.51  sup_time_sim_immed:                     0.
% 7.74/1.51  
% 7.74/1.51  sup_num_of_clauses:                     555
% 7.74/1.51  sup_num_in_active:                      145
% 7.74/1.51  sup_num_in_passive:                     410
% 7.74/1.51  sup_num_of_loops:                       203
% 7.74/1.51  sup_fw_superposition:                   577
% 7.74/1.51  sup_bw_superposition:                   428
% 7.74/1.51  sup_immediate_simplified:               243
% 7.74/1.51  sup_given_eliminated:                   5
% 7.74/1.51  comparisons_done:                       0
% 7.74/1.51  comparisons_avoided:                    5
% 7.74/1.51  
% 7.74/1.51  ------ Simplifications
% 7.74/1.51  
% 7.74/1.51  
% 7.74/1.51  sim_fw_subset_subsumed:                 72
% 7.74/1.51  sim_bw_subset_subsumed:                 70
% 7.74/1.51  sim_fw_subsumed:                        92
% 7.74/1.51  sim_bw_subsumed:                        52
% 7.74/1.51  sim_fw_subsumption_res:                 0
% 7.74/1.51  sim_bw_subsumption_res:                 0
% 7.74/1.51  sim_tautology_del:                      74
% 7.74/1.51  sim_eq_tautology_del:                   6
% 7.74/1.51  sim_eq_res_simp:                        0
% 7.74/1.51  sim_fw_demodulated:                     18
% 7.74/1.51  sim_bw_demodulated:                     0
% 7.74/1.51  sim_light_normalised:                   102
% 7.74/1.51  sim_joinable_taut:                      0
% 7.74/1.51  sim_joinable_simp:                      0
% 7.74/1.51  sim_ac_normalised:                      0
% 7.74/1.51  sim_smt_subsumption:                    0
% 7.74/1.51  
%------------------------------------------------------------------------------
