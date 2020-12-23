%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:30 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  235 (2817 expanded)
%              Number of clauses        :  133 ( 651 expanded)
%              Number of leaves         :   29 ( 549 expanded)
%              Depth                    :   27
%              Number of atoms          :  994 (23081 expanded)
%              Number of equality atoms :  224 ( 841 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK7)
          | ~ v1_subset_1(sK7,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK7)
          | v1_subset_1(sK7,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK7,X0)
        & ~ v1_xboole_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK6),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK6)) )
          & ( ~ r2_hidden(k3_yellow_0(sK6),X1)
            | v1_subset_1(X1,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
          & v13_waybel_0(X1,sK6)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK6)
      & v1_yellow_0(sK6)
      & v5_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( r2_hidden(k3_yellow_0(sK6),sK7)
      | ~ v1_subset_1(sK7,u1_struct_0(sK6)) )
    & ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
      | v1_subset_1(sK7,u1_struct_0(sK6)) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & v13_waybel_0(sK7,sK6)
    & ~ v1_xboole_0(sK7)
    & l1_orders_2(sK6)
    & v1_yellow_0(sK6)
    & v5_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f71,f73,f72])).

fof(f111,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f74])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r1_orders_2(X0,X2,sK5(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
            & r1_orders_2(X0,sK4(X0,X1),X3)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f100,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f99,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f109,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f116,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f74])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),X0)
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f53])).

fof(f81,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2609,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_951,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_38])).

cnf(c_952,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_951])).

cnf(c_2583,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_14,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_936,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_38])).

cnf(c_937,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_2584,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_15,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_915,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_38])).

cnf(c_916,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_2585,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_3679,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X3,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2584,c_2585])).

cnf(c_8377,plain,
    ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
    | r2_lattice3(sK6,X0,X2) != iProver_top
    | r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_3679])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2605,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_854,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_38])).

cnf(c_855,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_871,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_855,c_10])).

cnf(c_2589,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_871])).

cnf(c_4372,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_2589])).

cnf(c_36,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1031,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_871])).

cnf(c_1032,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1032,c_35])).

cnf(c_1035,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(renaming,[status(thm)],[c_1034])).

cnf(c_1036,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_4959,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4372,c_1036])).

cnf(c_9276,plain,
    ( r2_lattice3(sK6,X0,X1) != iProver_top
    | r2_lattice3(sK6,X0,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8377,c_4959])).

cnf(c_11576,plain,
    ( r2_lattice3(sK6,sK7,X0) != iProver_top
    | r2_lattice3(sK6,sK7,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_9276])).

cnf(c_45,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_23,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_76,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_78,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_2037,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2051,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_2027,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2058,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_3113,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_2028,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3080,plain,
    ( u1_struct_0(sK6) != X0
    | sK7 != X0
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2028])).

cnf(c_3597,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_20,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_22,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_22])).

cnf(c_259,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_24,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_39,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_594,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_595,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_40,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_74,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_597,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_41,c_40,c_39,c_38,c_74])).

cnf(c_693,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_597])).

cnf(c_694,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_694,c_38])).

cnf(c_699,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_698])).

cnf(c_2597,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_16,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_910,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_38])).

cnf(c_911,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_2707,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2597,c_911])).

cnf(c_4968,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2707,c_4959])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_37])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_5207,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_5208,plain,
    ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5207])).

cnf(c_31,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_33,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_337,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_337])).

cnf(c_632,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_634,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_35])).

cnf(c_2600,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_5415,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2600,c_4968])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2612,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_2602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_4863,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2612,c_2602])).

cnf(c_5704,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_4863])).

cnf(c_2031,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3025,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_3334,plain,
    ( m1_subset_1(k3_yellow_0(sK6),X0)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3025])).

cnf(c_7012,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | m1_subset_1(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3334])).

cnf(c_7015,plain,
    ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7012])).

cnf(c_11622,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11576,c_45,c_78,c_2051,c_2058,c_3113,c_3597,c_4968,c_5208,c_5415,c_5704,c_7015])).

cnf(c_11631,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6),X1,X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2609,c_11622])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3270,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_2613])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | ~ r2_hidden(sK0(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2611,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3964,plain,
    ( u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),X0) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3270,c_2611])).

cnf(c_15959,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11631,c_3964])).

cnf(c_16003,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15959,c_11631])).

cnf(c_894,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_895,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_2587,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_11630,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_11622])).

cnf(c_3015,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_3172,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3015])).

cnf(c_5305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | X0 != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3172])).

cnf(c_7804,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5305])).

cnf(c_7806,plain,
    ( u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
    | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7804])).

cnf(c_5,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_609,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_613,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_6])).

cnf(c_4550,plain,
    ( u1_struct_0(sK6) = sK1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_3173,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_4010,plain,
    ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3173])).

cnf(c_2966,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2972,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2966])).

cnf(c_34,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_335,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_34])).

cnf(c_619,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK1(X0) != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_335])).

cnf(c_620,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK1(u1_struct_0(sK6)) != sK7 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_2601,plain,
    ( sK1(u1_struct_0(sK6)) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_2646,plain,
    ( u1_struct_0(sK6) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2601,c_613])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16003,c_11630,c_7806,c_4550,c_4010,c_2972,c_2646,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/1.00  
% 3.96/1.00  ------  iProver source info
% 3.96/1.00  
% 3.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/1.00  git: non_committed_changes: false
% 3.96/1.00  git: last_make_outside_of_git: false
% 3.96/1.00  
% 3.96/1.00  ------ 
% 3.96/1.00  
% 3.96/1.00  ------ Input Options
% 3.96/1.00  
% 3.96/1.00  --out_options                           all
% 3.96/1.00  --tptp_safe_out                         true
% 3.96/1.00  --problem_path                          ""
% 3.96/1.00  --include_path                          ""
% 3.96/1.00  --clausifier                            res/vclausify_rel
% 3.96/1.00  --clausifier_options                    --mode clausify
% 3.96/1.00  --stdin                                 false
% 3.96/1.00  --stats_out                             all
% 3.96/1.00  
% 3.96/1.00  ------ General Options
% 3.96/1.00  
% 3.96/1.00  --fof                                   false
% 3.96/1.00  --time_out_real                         305.
% 3.96/1.00  --time_out_virtual                      -1.
% 3.96/1.00  --symbol_type_check                     false
% 3.96/1.00  --clausify_out                          false
% 3.96/1.00  --sig_cnt_out                           false
% 3.96/1.00  --trig_cnt_out                          false
% 3.96/1.00  --trig_cnt_out_tolerance                1.
% 3.96/1.00  --trig_cnt_out_sk_spl                   false
% 3.96/1.00  --abstr_cl_out                          false
% 3.96/1.00  
% 3.96/1.00  ------ Global Options
% 3.96/1.00  
% 3.96/1.00  --schedule                              default
% 3.96/1.00  --add_important_lit                     false
% 3.96/1.00  --prop_solver_per_cl                    1000
% 3.96/1.00  --min_unsat_core                        false
% 3.96/1.00  --soft_assumptions                      false
% 3.96/1.00  --soft_lemma_size                       3
% 3.96/1.00  --prop_impl_unit_size                   0
% 3.96/1.00  --prop_impl_unit                        []
% 3.96/1.00  --share_sel_clauses                     true
% 3.96/1.00  --reset_solvers                         false
% 3.96/1.00  --bc_imp_inh                            [conj_cone]
% 3.96/1.00  --conj_cone_tolerance                   3.
% 3.96/1.00  --extra_neg_conj                        none
% 3.96/1.00  --large_theory_mode                     true
% 3.96/1.00  --prolific_symb_bound                   200
% 3.96/1.00  --lt_threshold                          2000
% 3.96/1.00  --clause_weak_htbl                      true
% 3.96/1.00  --gc_record_bc_elim                     false
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing Options
% 3.96/1.00  
% 3.96/1.00  --preprocessing_flag                    true
% 3.96/1.00  --time_out_prep_mult                    0.1
% 3.96/1.00  --splitting_mode                        input
% 3.96/1.00  --splitting_grd                         true
% 3.96/1.00  --splitting_cvd                         false
% 3.96/1.00  --splitting_cvd_svl                     false
% 3.96/1.00  --splitting_nvd                         32
% 3.96/1.00  --sub_typing                            true
% 3.96/1.00  --prep_gs_sim                           true
% 3.96/1.00  --prep_unflatten                        true
% 3.96/1.00  --prep_res_sim                          true
% 3.96/1.00  --prep_upred                            true
% 3.96/1.00  --prep_sem_filter                       exhaustive
% 3.96/1.00  --prep_sem_filter_out                   false
% 3.96/1.00  --pred_elim                             true
% 3.96/1.00  --res_sim_input                         true
% 3.96/1.00  --eq_ax_congr_red                       true
% 3.96/1.00  --pure_diseq_elim                       true
% 3.96/1.00  --brand_transform                       false
% 3.96/1.00  --non_eq_to_eq                          false
% 3.96/1.00  --prep_def_merge                        true
% 3.96/1.00  --prep_def_merge_prop_impl              false
% 3.96/1.00  --prep_def_merge_mbd                    true
% 3.96/1.00  --prep_def_merge_tr_red                 false
% 3.96/1.00  --prep_def_merge_tr_cl                  false
% 3.96/1.00  --smt_preprocessing                     true
% 3.96/1.00  --smt_ac_axioms                         fast
% 3.96/1.00  --preprocessed_out                      false
% 3.96/1.00  --preprocessed_stats                    false
% 3.96/1.00  
% 3.96/1.00  ------ Abstraction refinement Options
% 3.96/1.00  
% 3.96/1.00  --abstr_ref                             []
% 3.96/1.00  --abstr_ref_prep                        false
% 3.96/1.00  --abstr_ref_until_sat                   false
% 3.96/1.00  --abstr_ref_sig_restrict                funpre
% 3.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.00  --abstr_ref_under                       []
% 3.96/1.00  
% 3.96/1.00  ------ SAT Options
% 3.96/1.00  
% 3.96/1.00  --sat_mode                              false
% 3.96/1.00  --sat_fm_restart_options                ""
% 3.96/1.00  --sat_gr_def                            false
% 3.96/1.00  --sat_epr_types                         true
% 3.96/1.00  --sat_non_cyclic_types                  false
% 3.96/1.00  --sat_finite_models                     false
% 3.96/1.00  --sat_fm_lemmas                         false
% 3.96/1.00  --sat_fm_prep                           false
% 3.96/1.00  --sat_fm_uc_incr                        true
% 3.96/1.00  --sat_out_model                         small
% 3.96/1.00  --sat_out_clauses                       false
% 3.96/1.00  
% 3.96/1.00  ------ QBF Options
% 3.96/1.00  
% 3.96/1.00  --qbf_mode                              false
% 3.96/1.00  --qbf_elim_univ                         false
% 3.96/1.00  --qbf_dom_inst                          none
% 3.96/1.00  --qbf_dom_pre_inst                      false
% 3.96/1.00  --qbf_sk_in                             false
% 3.96/1.00  --qbf_pred_elim                         true
% 3.96/1.00  --qbf_split                             512
% 3.96/1.00  
% 3.96/1.00  ------ BMC1 Options
% 3.96/1.00  
% 3.96/1.00  --bmc1_incremental                      false
% 3.96/1.00  --bmc1_axioms                           reachable_all
% 3.96/1.00  --bmc1_min_bound                        0
% 3.96/1.00  --bmc1_max_bound                        -1
% 3.96/1.00  --bmc1_max_bound_default                -1
% 3.96/1.00  --bmc1_symbol_reachability              true
% 3.96/1.00  --bmc1_property_lemmas                  false
% 3.96/1.00  --bmc1_k_induction                      false
% 3.96/1.00  --bmc1_non_equiv_states                 false
% 3.96/1.00  --bmc1_deadlock                         false
% 3.96/1.00  --bmc1_ucm                              false
% 3.96/1.00  --bmc1_add_unsat_core                   none
% 3.96/1.00  --bmc1_unsat_core_children              false
% 3.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.00  --bmc1_out_stat                         full
% 3.96/1.00  --bmc1_ground_init                      false
% 3.96/1.00  --bmc1_pre_inst_next_state              false
% 3.96/1.00  --bmc1_pre_inst_state                   false
% 3.96/1.00  --bmc1_pre_inst_reach_state             false
% 3.96/1.00  --bmc1_out_unsat_core                   false
% 3.96/1.00  --bmc1_aig_witness_out                  false
% 3.96/1.00  --bmc1_verbose                          false
% 3.96/1.00  --bmc1_dump_clauses_tptp                false
% 3.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.00  --bmc1_dump_file                        -
% 3.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.00  --bmc1_ucm_extend_mode                  1
% 3.96/1.00  --bmc1_ucm_init_mode                    2
% 3.96/1.00  --bmc1_ucm_cone_mode                    none
% 3.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.00  --bmc1_ucm_relax_model                  4
% 3.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.00  --bmc1_ucm_layered_model                none
% 3.96/1.00  --bmc1_ucm_max_lemma_size               10
% 3.96/1.00  
% 3.96/1.00  ------ AIG Options
% 3.96/1.00  
% 3.96/1.00  --aig_mode                              false
% 3.96/1.00  
% 3.96/1.00  ------ Instantiation Options
% 3.96/1.00  
% 3.96/1.00  --instantiation_flag                    true
% 3.96/1.00  --inst_sos_flag                         false
% 3.96/1.00  --inst_sos_phase                        true
% 3.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.00  --inst_lit_sel_side                     num_symb
% 3.96/1.00  --inst_solver_per_active                1400
% 3.96/1.00  --inst_solver_calls_frac                1.
% 3.96/1.00  --inst_passive_queue_type               priority_queues
% 3.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.00  --inst_passive_queues_freq              [25;2]
% 3.96/1.00  --inst_dismatching                      true
% 3.96/1.00  --inst_eager_unprocessed_to_passive     true
% 3.96/1.00  --inst_prop_sim_given                   true
% 3.96/1.00  --inst_prop_sim_new                     false
% 3.96/1.00  --inst_subs_new                         false
% 3.96/1.00  --inst_eq_res_simp                      false
% 3.96/1.00  --inst_subs_given                       false
% 3.96/1.00  --inst_orphan_elimination               true
% 3.96/1.00  --inst_learning_loop_flag               true
% 3.96/1.00  --inst_learning_start                   3000
% 3.96/1.00  --inst_learning_factor                  2
% 3.96/1.00  --inst_start_prop_sim_after_learn       3
% 3.96/1.00  --inst_sel_renew                        solver
% 3.96/1.00  --inst_lit_activity_flag                true
% 3.96/1.00  --inst_restr_to_given                   false
% 3.96/1.00  --inst_activity_threshold               500
% 3.96/1.00  --inst_out_proof                        true
% 3.96/1.00  
% 3.96/1.00  ------ Resolution Options
% 3.96/1.00  
% 3.96/1.00  --resolution_flag                       true
% 3.96/1.00  --res_lit_sel                           adaptive
% 3.96/1.00  --res_lit_sel_side                      none
% 3.96/1.00  --res_ordering                          kbo
% 3.96/1.00  --res_to_prop_solver                    active
% 3.96/1.00  --res_prop_simpl_new                    false
% 3.96/1.00  --res_prop_simpl_given                  true
% 3.96/1.00  --res_passive_queue_type                priority_queues
% 3.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.00  --res_passive_queues_freq               [15;5]
% 3.96/1.00  --res_forward_subs                      full
% 3.96/1.00  --res_backward_subs                     full
% 3.96/1.00  --res_forward_subs_resolution           true
% 3.96/1.00  --res_backward_subs_resolution          true
% 3.96/1.00  --res_orphan_elimination                true
% 3.96/1.00  --res_time_limit                        2.
% 3.96/1.00  --res_out_proof                         true
% 3.96/1.00  
% 3.96/1.00  ------ Superposition Options
% 3.96/1.00  
% 3.96/1.00  --superposition_flag                    true
% 3.96/1.00  --sup_passive_queue_type                priority_queues
% 3.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.00  --demod_completeness_check              fast
% 3.96/1.00  --demod_use_ground                      true
% 3.96/1.00  --sup_to_prop_solver                    passive
% 3.96/1.00  --sup_prop_simpl_new                    true
% 3.96/1.00  --sup_prop_simpl_given                  true
% 3.96/1.00  --sup_fun_splitting                     false
% 3.96/1.00  --sup_smt_interval                      50000
% 3.96/1.00  
% 3.96/1.00  ------ Superposition Simplification Setup
% 3.96/1.00  
% 3.96/1.00  --sup_indices_passive                   []
% 3.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_full_bw                           [BwDemod]
% 3.96/1.00  --sup_immed_triv                        [TrivRules]
% 3.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_immed_bw_main                     []
% 3.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.00  
% 3.96/1.00  ------ Combination Options
% 3.96/1.00  
% 3.96/1.00  --comb_res_mult                         3
% 3.96/1.00  --comb_sup_mult                         2
% 3.96/1.00  --comb_inst_mult                        10
% 3.96/1.00  
% 3.96/1.00  ------ Debug Options
% 3.96/1.00  
% 3.96/1.00  --dbg_backtrace                         false
% 3.96/1.00  --dbg_dump_prop_clauses                 false
% 3.96/1.00  --dbg_dump_prop_clauses_file            -
% 3.96/1.00  --dbg_out_stat                          false
% 3.96/1.00  ------ Parsing...
% 3.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/1.00  ------ Proving...
% 3.96/1.00  ------ Problem Properties 
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  clauses                                 34
% 3.96/1.00  conjectures                             2
% 3.96/1.00  EPR                                     3
% 3.96/1.00  Horn                                    23
% 3.96/1.00  unary                                   9
% 3.96/1.00  binary                                  5
% 3.96/1.00  lits                                    92
% 3.96/1.00  lits eq                                 11
% 3.96/1.00  fd_pure                                 0
% 3.96/1.00  fd_pseudo                               0
% 3.96/1.00  fd_cond                                 3
% 3.96/1.00  fd_pseudo_cond                          3
% 3.96/1.00  AC symbols                              0
% 3.96/1.00  
% 3.96/1.00  ------ Schedule dynamic 5 is on 
% 3.96/1.00  
% 3.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ 
% 3.96/1.00  Current options:
% 3.96/1.00  ------ 
% 3.96/1.00  
% 3.96/1.00  ------ Input Options
% 3.96/1.00  
% 3.96/1.00  --out_options                           all
% 3.96/1.00  --tptp_safe_out                         true
% 3.96/1.00  --problem_path                          ""
% 3.96/1.00  --include_path                          ""
% 3.96/1.00  --clausifier                            res/vclausify_rel
% 3.96/1.00  --clausifier_options                    --mode clausify
% 3.96/1.00  --stdin                                 false
% 3.96/1.00  --stats_out                             all
% 3.96/1.00  
% 3.96/1.00  ------ General Options
% 3.96/1.00  
% 3.96/1.00  --fof                                   false
% 3.96/1.00  --time_out_real                         305.
% 3.96/1.00  --time_out_virtual                      -1.
% 3.96/1.00  --symbol_type_check                     false
% 3.96/1.00  --clausify_out                          false
% 3.96/1.00  --sig_cnt_out                           false
% 3.96/1.00  --trig_cnt_out                          false
% 3.96/1.00  --trig_cnt_out_tolerance                1.
% 3.96/1.00  --trig_cnt_out_sk_spl                   false
% 3.96/1.00  --abstr_cl_out                          false
% 3.96/1.00  
% 3.96/1.00  ------ Global Options
% 3.96/1.00  
% 3.96/1.00  --schedule                              default
% 3.96/1.00  --add_important_lit                     false
% 3.96/1.00  --prop_solver_per_cl                    1000
% 3.96/1.00  --min_unsat_core                        false
% 3.96/1.00  --soft_assumptions                      false
% 3.96/1.00  --soft_lemma_size                       3
% 3.96/1.00  --prop_impl_unit_size                   0
% 3.96/1.00  --prop_impl_unit                        []
% 3.96/1.00  --share_sel_clauses                     true
% 3.96/1.00  --reset_solvers                         false
% 3.96/1.00  --bc_imp_inh                            [conj_cone]
% 3.96/1.00  --conj_cone_tolerance                   3.
% 3.96/1.00  --extra_neg_conj                        none
% 3.96/1.00  --large_theory_mode                     true
% 3.96/1.00  --prolific_symb_bound                   200
% 3.96/1.00  --lt_threshold                          2000
% 3.96/1.00  --clause_weak_htbl                      true
% 3.96/1.00  --gc_record_bc_elim                     false
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing Options
% 3.96/1.00  
% 3.96/1.00  --preprocessing_flag                    true
% 3.96/1.00  --time_out_prep_mult                    0.1
% 3.96/1.00  --splitting_mode                        input
% 3.96/1.00  --splitting_grd                         true
% 3.96/1.00  --splitting_cvd                         false
% 3.96/1.00  --splitting_cvd_svl                     false
% 3.96/1.00  --splitting_nvd                         32
% 3.96/1.00  --sub_typing                            true
% 3.96/1.00  --prep_gs_sim                           true
% 3.96/1.00  --prep_unflatten                        true
% 3.96/1.00  --prep_res_sim                          true
% 3.96/1.00  --prep_upred                            true
% 3.96/1.00  --prep_sem_filter                       exhaustive
% 3.96/1.00  --prep_sem_filter_out                   false
% 3.96/1.00  --pred_elim                             true
% 3.96/1.00  --res_sim_input                         true
% 3.96/1.00  --eq_ax_congr_red                       true
% 3.96/1.00  --pure_diseq_elim                       true
% 3.96/1.00  --brand_transform                       false
% 3.96/1.00  --non_eq_to_eq                          false
% 3.96/1.00  --prep_def_merge                        true
% 3.96/1.00  --prep_def_merge_prop_impl              false
% 3.96/1.00  --prep_def_merge_mbd                    true
% 3.96/1.00  --prep_def_merge_tr_red                 false
% 3.96/1.00  --prep_def_merge_tr_cl                  false
% 3.96/1.00  --smt_preprocessing                     true
% 3.96/1.00  --smt_ac_axioms                         fast
% 3.96/1.00  --preprocessed_out                      false
% 3.96/1.00  --preprocessed_stats                    false
% 3.96/1.00  
% 3.96/1.00  ------ Abstraction refinement Options
% 3.96/1.00  
% 3.96/1.00  --abstr_ref                             []
% 3.96/1.00  --abstr_ref_prep                        false
% 3.96/1.00  --abstr_ref_until_sat                   false
% 3.96/1.00  --abstr_ref_sig_restrict                funpre
% 3.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/1.00  --abstr_ref_under                       []
% 3.96/1.00  
% 3.96/1.00  ------ SAT Options
% 3.96/1.00  
% 3.96/1.00  --sat_mode                              false
% 3.96/1.00  --sat_fm_restart_options                ""
% 3.96/1.00  --sat_gr_def                            false
% 3.96/1.00  --sat_epr_types                         true
% 3.96/1.00  --sat_non_cyclic_types                  false
% 3.96/1.00  --sat_finite_models                     false
% 3.96/1.00  --sat_fm_lemmas                         false
% 3.96/1.00  --sat_fm_prep                           false
% 3.96/1.00  --sat_fm_uc_incr                        true
% 3.96/1.00  --sat_out_model                         small
% 3.96/1.00  --sat_out_clauses                       false
% 3.96/1.00  
% 3.96/1.00  ------ QBF Options
% 3.96/1.00  
% 3.96/1.00  --qbf_mode                              false
% 3.96/1.00  --qbf_elim_univ                         false
% 3.96/1.00  --qbf_dom_inst                          none
% 3.96/1.00  --qbf_dom_pre_inst                      false
% 3.96/1.00  --qbf_sk_in                             false
% 3.96/1.00  --qbf_pred_elim                         true
% 3.96/1.00  --qbf_split                             512
% 3.96/1.00  
% 3.96/1.00  ------ BMC1 Options
% 3.96/1.00  
% 3.96/1.00  --bmc1_incremental                      false
% 3.96/1.00  --bmc1_axioms                           reachable_all
% 3.96/1.00  --bmc1_min_bound                        0
% 3.96/1.00  --bmc1_max_bound                        -1
% 3.96/1.00  --bmc1_max_bound_default                -1
% 3.96/1.00  --bmc1_symbol_reachability              true
% 3.96/1.00  --bmc1_property_lemmas                  false
% 3.96/1.00  --bmc1_k_induction                      false
% 3.96/1.00  --bmc1_non_equiv_states                 false
% 3.96/1.00  --bmc1_deadlock                         false
% 3.96/1.00  --bmc1_ucm                              false
% 3.96/1.00  --bmc1_add_unsat_core                   none
% 3.96/1.00  --bmc1_unsat_core_children              false
% 3.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/1.00  --bmc1_out_stat                         full
% 3.96/1.00  --bmc1_ground_init                      false
% 3.96/1.00  --bmc1_pre_inst_next_state              false
% 3.96/1.00  --bmc1_pre_inst_state                   false
% 3.96/1.00  --bmc1_pre_inst_reach_state             false
% 3.96/1.00  --bmc1_out_unsat_core                   false
% 3.96/1.00  --bmc1_aig_witness_out                  false
% 3.96/1.00  --bmc1_verbose                          false
% 3.96/1.00  --bmc1_dump_clauses_tptp                false
% 3.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.96/1.00  --bmc1_dump_file                        -
% 3.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.96/1.00  --bmc1_ucm_extend_mode                  1
% 3.96/1.00  --bmc1_ucm_init_mode                    2
% 3.96/1.00  --bmc1_ucm_cone_mode                    none
% 3.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.96/1.00  --bmc1_ucm_relax_model                  4
% 3.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/1.00  --bmc1_ucm_layered_model                none
% 3.96/1.00  --bmc1_ucm_max_lemma_size               10
% 3.96/1.00  
% 3.96/1.00  ------ AIG Options
% 3.96/1.00  
% 3.96/1.00  --aig_mode                              false
% 3.96/1.00  
% 3.96/1.00  ------ Instantiation Options
% 3.96/1.00  
% 3.96/1.00  --instantiation_flag                    true
% 3.96/1.00  --inst_sos_flag                         false
% 3.96/1.00  --inst_sos_phase                        true
% 3.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/1.00  --inst_lit_sel_side                     none
% 3.96/1.00  --inst_solver_per_active                1400
% 3.96/1.00  --inst_solver_calls_frac                1.
% 3.96/1.00  --inst_passive_queue_type               priority_queues
% 3.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/1.00  --inst_passive_queues_freq              [25;2]
% 3.96/1.00  --inst_dismatching                      true
% 3.96/1.00  --inst_eager_unprocessed_to_passive     true
% 3.96/1.00  --inst_prop_sim_given                   true
% 3.96/1.00  --inst_prop_sim_new                     false
% 3.96/1.00  --inst_subs_new                         false
% 3.96/1.00  --inst_eq_res_simp                      false
% 3.96/1.00  --inst_subs_given                       false
% 3.96/1.00  --inst_orphan_elimination               true
% 3.96/1.00  --inst_learning_loop_flag               true
% 3.96/1.00  --inst_learning_start                   3000
% 3.96/1.00  --inst_learning_factor                  2
% 3.96/1.00  --inst_start_prop_sim_after_learn       3
% 3.96/1.00  --inst_sel_renew                        solver
% 3.96/1.00  --inst_lit_activity_flag                true
% 3.96/1.00  --inst_restr_to_given                   false
% 3.96/1.00  --inst_activity_threshold               500
% 3.96/1.00  --inst_out_proof                        true
% 3.96/1.00  
% 3.96/1.00  ------ Resolution Options
% 3.96/1.00  
% 3.96/1.00  --resolution_flag                       false
% 3.96/1.00  --res_lit_sel                           adaptive
% 3.96/1.00  --res_lit_sel_side                      none
% 3.96/1.00  --res_ordering                          kbo
% 3.96/1.00  --res_to_prop_solver                    active
% 3.96/1.00  --res_prop_simpl_new                    false
% 3.96/1.00  --res_prop_simpl_given                  true
% 3.96/1.00  --res_passive_queue_type                priority_queues
% 3.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/1.00  --res_passive_queues_freq               [15;5]
% 3.96/1.00  --res_forward_subs                      full
% 3.96/1.00  --res_backward_subs                     full
% 3.96/1.00  --res_forward_subs_resolution           true
% 3.96/1.00  --res_backward_subs_resolution          true
% 3.96/1.00  --res_orphan_elimination                true
% 3.96/1.00  --res_time_limit                        2.
% 3.96/1.00  --res_out_proof                         true
% 3.96/1.00  
% 3.96/1.00  ------ Superposition Options
% 3.96/1.00  
% 3.96/1.00  --superposition_flag                    true
% 3.96/1.00  --sup_passive_queue_type                priority_queues
% 3.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.96/1.00  --demod_completeness_check              fast
% 3.96/1.00  --demod_use_ground                      true
% 3.96/1.00  --sup_to_prop_solver                    passive
% 3.96/1.00  --sup_prop_simpl_new                    true
% 3.96/1.00  --sup_prop_simpl_given                  true
% 3.96/1.00  --sup_fun_splitting                     false
% 3.96/1.00  --sup_smt_interval                      50000
% 3.96/1.00  
% 3.96/1.00  ------ Superposition Simplification Setup
% 3.96/1.00  
% 3.96/1.00  --sup_indices_passive                   []
% 3.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_full_bw                           [BwDemod]
% 3.96/1.00  --sup_immed_triv                        [TrivRules]
% 3.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_immed_bw_main                     []
% 3.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/1.00  
% 3.96/1.00  ------ Combination Options
% 3.96/1.00  
% 3.96/1.00  --comb_res_mult                         3
% 3.96/1.00  --comb_sup_mult                         2
% 3.96/1.00  --comb_inst_mult                        10
% 3.96/1.00  
% 3.96/1.00  ------ Debug Options
% 3.96/1.00  
% 3.96/1.00  --dbg_backtrace                         false
% 3.96/1.00  --dbg_dump_prop_clauses                 false
% 3.96/1.00  --dbg_dump_prop_clauses_file            -
% 3.96/1.00  --dbg_out_stat                          false
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  ------ Proving...
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  % SZS status Theorem for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  fof(f3,axiom,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f26,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(ennf_transformation,[],[f3])).
% 3.96/1.00  
% 3.96/1.00  fof(f27,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(flattening,[],[f26])).
% 3.96/1.00  
% 3.96/1.00  fof(f49,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(nnf_transformation,[],[f27])).
% 3.96/1.00  
% 3.96/1.00  fof(f50,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(flattening,[],[f49])).
% 3.96/1.00  
% 3.96/1.00  fof(f51,plain,(
% 3.96/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f52,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.96/1.00  
% 3.96/1.00  fof(f77,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f52])).
% 3.96/1.00  
% 3.96/1.00  fof(f10,axiom,(
% 3.96/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f35,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f10])).
% 3.96/1.00  
% 3.96/1.00  fof(f36,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(flattening,[],[f35])).
% 3.96/1.00  
% 3.96/1.00  fof(f55,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(nnf_transformation,[],[f36])).
% 3.96/1.00  
% 3.96/1.00  fof(f56,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(rectify,[],[f55])).
% 3.96/1.00  
% 3.96/1.00  fof(f57,plain,(
% 3.96/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f58,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f56,f57])).
% 3.96/1.00  
% 3.96/1.00  fof(f89,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f58])).
% 3.96/1.00  
% 3.96/1.00  fof(f18,conjecture,(
% 3.96/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f19,negated_conjecture,(
% 3.96/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.96/1.00    inference(negated_conjecture,[],[f18])).
% 3.96/1.00  
% 3.96/1.00  fof(f21,plain,(
% 3.96/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.96/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.96/1.00  
% 3.96/1.00  fof(f22,plain,(
% 3.96/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.96/1.00    inference(pure_predicate_removal,[],[f21])).
% 3.96/1.00  
% 3.96/1.00  fof(f23,plain,(
% 3.96/1.00    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.96/1.00    inference(pure_predicate_removal,[],[f22])).
% 3.96/1.00  
% 3.96/1.00  fof(f47,plain,(
% 3.96/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.96/1.00    inference(ennf_transformation,[],[f23])).
% 3.96/1.00  
% 3.96/1.00  fof(f48,plain,(
% 3.96/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.96/1.00    inference(flattening,[],[f47])).
% 3.96/1.00  
% 3.96/1.00  fof(f70,plain,(
% 3.96/1.00    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.96/1.00    inference(nnf_transformation,[],[f48])).
% 3.96/1.00  
% 3.96/1.00  fof(f71,plain,(
% 3.96/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.96/1.00    inference(flattening,[],[f70])).
% 3.96/1.00  
% 3.96/1.00  fof(f73,plain,(
% 3.96/1.00    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f72,plain,(
% 3.96/1.00    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f74,plain,(
% 3.96/1.00    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f71,f73,f72])).
% 3.96/1.00  
% 3.96/1.00  fof(f111,plain,(
% 3.96/1.00    l1_orders_2(sK6)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f88,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f58])).
% 3.96/1.00  
% 3.96/1.00  fof(f87,plain,(
% 3.96/1.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f58])).
% 3.96/1.00  
% 3.96/1.00  fof(f114,plain,(
% 3.96/1.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f16,axiom,(
% 3.96/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f44,plain,(
% 3.96/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f16])).
% 3.96/1.00  
% 3.96/1.00  fof(f45,plain,(
% 3.96/1.00    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(flattening,[],[f44])).
% 3.96/1.00  
% 3.96/1.00  fof(f64,plain,(
% 3.96/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(nnf_transformation,[],[f45])).
% 3.96/1.00  
% 3.96/1.00  fof(f65,plain,(
% 3.96/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(rectify,[],[f64])).
% 3.96/1.00  
% 3.96/1.00  fof(f67,plain,(
% 3.96/1.00    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f66,plain,(
% 3.96/1.00    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f68,plain,(
% 3.96/1.00    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).
% 3.96/1.00  
% 3.96/1.00  fof(f100,plain,(
% 3.96/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f68])).
% 3.96/1.00  
% 3.96/1.00  fof(f8,axiom,(
% 3.96/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f32,plain,(
% 3.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.96/1.00    inference(ennf_transformation,[],[f8])).
% 3.96/1.00  
% 3.96/1.00  fof(f33,plain,(
% 3.96/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.96/1.00    inference(flattening,[],[f32])).
% 3.96/1.00  
% 3.96/1.00  fof(f85,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f33])).
% 3.96/1.00  
% 3.96/1.00  fof(f113,plain,(
% 3.96/1.00    v13_waybel_0(sK7,sK6)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f14,axiom,(
% 3.96/1.00    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f41,plain,(
% 3.96/1.00    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f14])).
% 3.96/1.00  
% 3.96/1.00  fof(f98,plain,(
% 3.96/1.00    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f41])).
% 3.96/1.00  
% 3.96/1.00  fof(f12,axiom,(
% 3.96/1.00    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f38,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f12])).
% 3.96/1.00  
% 3.96/1.00  fof(f39,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(flattening,[],[f38])).
% 3.96/1.00  
% 3.96/1.00  fof(f59,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(nnf_transformation,[],[f39])).
% 3.96/1.00  
% 3.96/1.00  fof(f60,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(flattening,[],[f59])).
% 3.96/1.00  
% 3.96/1.00  fof(f61,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(rectify,[],[f60])).
% 3.96/1.00  
% 3.96/1.00  fof(f62,plain,(
% 3.96/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f63,plain,(
% 3.96/1.00    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f61,f62])).
% 3.96/1.00  
% 3.96/1.00  fof(f93,plain,(
% 3.96/1.00    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f63])).
% 3.96/1.00  
% 3.96/1.00  fof(f117,plain,(
% 3.96/1.00    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(equality_resolution,[],[f93])).
% 3.96/1.00  
% 3.96/1.00  fof(f13,axiom,(
% 3.96/1.00    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f40,plain,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f13])).
% 3.96/1.00  
% 3.96/1.00  fof(f97,plain,(
% 3.96/1.00    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f40])).
% 3.96/1.00  
% 3.96/1.00  fof(f15,axiom,(
% 3.96/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f24,plain,(
% 3.96/1.00    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.96/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.96/1.00  
% 3.96/1.00  fof(f42,plain,(
% 3.96/1.00    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.96/1.00    inference(ennf_transformation,[],[f24])).
% 3.96/1.00  
% 3.96/1.00  fof(f43,plain,(
% 3.96/1.00    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.96/1.00    inference(flattening,[],[f42])).
% 3.96/1.00  
% 3.96/1.00  fof(f99,plain,(
% 3.96/1.00    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f43])).
% 3.96/1.00  
% 3.96/1.00  fof(f110,plain,(
% 3.96/1.00    v1_yellow_0(sK6)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f108,plain,(
% 3.96/1.00    ~v2_struct_0(sK6)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f109,plain,(
% 3.96/1.00    v5_orders_2(sK6)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f11,axiom,(
% 3.96/1.00    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f37,plain,(
% 3.96/1.00    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.96/1.00    inference(ennf_transformation,[],[f11])).
% 3.96/1.00  
% 3.96/1.00  fof(f91,plain,(
% 3.96/1.00    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f37])).
% 3.96/1.00  
% 3.96/1.00  fof(f6,axiom,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f29,plain,(
% 3.96/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.96/1.00    inference(ennf_transformation,[],[f6])).
% 3.96/1.00  
% 3.96/1.00  fof(f30,plain,(
% 3.96/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.96/1.00    inference(flattening,[],[f29])).
% 3.96/1.00  
% 3.96/1.00  fof(f83,plain,(
% 3.96/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f30])).
% 3.96/1.00  
% 3.96/1.00  fof(f112,plain,(
% 3.96/1.00    ~v1_xboole_0(sK7)),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f17,axiom,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f46,plain,(
% 3.96/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(ennf_transformation,[],[f17])).
% 3.96/1.00  
% 3.96/1.00  fof(f69,plain,(
% 3.96/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(nnf_transformation,[],[f46])).
% 3.96/1.00  
% 3.96/1.00  fof(f107,plain,(
% 3.96/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f69])).
% 3.96/1.00  
% 3.96/1.00  fof(f116,plain,(
% 3.96/1.00    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  fof(f2,axiom,(
% 3.96/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f76,plain,(
% 3.96/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f2])).
% 3.96/1.00  
% 3.96/1.00  fof(f7,axiom,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f20,plain,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.96/1.00    inference(unused_predicate_definition_removal,[],[f7])).
% 3.96/1.00  
% 3.96/1.00  fof(f31,plain,(
% 3.96/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.96/1.00    inference(ennf_transformation,[],[f20])).
% 3.96/1.00  
% 3.96/1.00  fof(f84,plain,(
% 3.96/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f31])).
% 3.96/1.00  
% 3.96/1.00  fof(f9,axiom,(
% 3.96/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f34,plain,(
% 3.96/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.96/1.00    inference(ennf_transformation,[],[f9])).
% 3.96/1.00  
% 3.96/1.00  fof(f86,plain,(
% 3.96/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f34])).
% 3.96/1.00  
% 3.96/1.00  fof(f1,axiom,(
% 3.96/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f25,plain,(
% 3.96/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(ennf_transformation,[],[f1])).
% 3.96/1.00  
% 3.96/1.00  fof(f75,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f25])).
% 3.96/1.00  
% 3.96/1.00  fof(f79,plain,(
% 3.96/1.00    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f52])).
% 3.96/1.00  
% 3.96/1.00  fof(f4,axiom,(
% 3.96/1.00    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/1.00  
% 3.96/1.00  fof(f53,plain,(
% 3.96/1.00    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.96/1.00    introduced(choice_axiom,[])).
% 3.96/1.00  
% 3.96/1.00  fof(f54,plain,(
% 3.96/1.00    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f4,f53])).
% 3.96/1.00  
% 3.96/1.00  fof(f81,plain,(
% 3.96/1.00    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 3.96/1.00    inference(cnf_transformation,[],[f54])).
% 3.96/1.00  
% 3.96/1.00  fof(f80,plain,(
% 3.96/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.96/1.00    inference(cnf_transformation,[],[f54])).
% 3.96/1.00  
% 3.96/1.00  fof(f115,plain,(
% 3.96/1.00    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.96/1.00    inference(cnf_transformation,[],[f74])).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.96/1.00      | m1_subset_1(sK0(X1,X0,X2),X1)
% 3.96/1.00      | X0 = X2 ),
% 3.96/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2609,plain,
% 3.96/1.00      ( X0 = X1
% 3.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.96/1.00      | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_13,plain,
% 3.96/1.00      ( r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_38,negated_conjecture,
% 3.96/1.00      ( l1_orders_2(sK6) ),
% 3.96/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_951,plain,
% 3.96/1.00      ( r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.96/1.00      | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_952,plain,
% 3.96/1.00      ( r2_lattice3(sK6,X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_951]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2583,plain,
% 3.96/1.00      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_14,plain,
% 3.96/1.00      ( r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_936,plain,
% 3.96/1.00      ( r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
% 3.96/1.00      | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_937,plain,
% 3.96/1.00      ( r2_lattice3(sK6,X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_936]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2584,plain,
% 3.96/1.00      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(sK2(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_15,plain,
% 3.96/1.00      ( r1_orders_2(X0,X1,X2)
% 3.96/1.00      | ~ r2_lattice3(X0,X3,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.96/1.00      | ~ r2_hidden(X1,X3)
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_915,plain,
% 3.96/1.00      ( r1_orders_2(X0,X1,X2)
% 3.96/1.00      | ~ r2_lattice3(X0,X3,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.96/1.00      | ~ r2_hidden(X1,X3)
% 3.96/1.00      | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_916,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ r2_lattice3(sK6,X2,X1)
% 3.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ r2_hidden(X0,X2) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_915]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2585,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3679,plain,
% 3.96/1.00      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X3,X2) != iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(sK2(sK6,X0,X1),X3) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2584,c_2585]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8377,plain,
% 3.96/1.00      ( r1_orders_2(sK6,sK2(sK6,X0,X1),X2) = iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X0,X2) != iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X0,X1) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2583,c_3679]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_35,negated_conjecture,
% 3.96/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.96/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2605,plain,
% 3.96/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_30,plain,
% 3.96/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.96/1.00      | ~ v13_waybel_0(X3,X0)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.96/1.00      | ~ r2_hidden(X1,X3)
% 3.96/1.00      | r2_hidden(X2,X3)
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_854,plain,
% 3.96/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 3.96/1.00      | ~ v13_waybel_0(X3,X0)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.96/1.00      | ~ r2_hidden(X1,X3)
% 3.96/1.00      | r2_hidden(X2,X3)
% 3.96/1.00      | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_855,plain,
% 3.96/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ v13_waybel_0(X2,sK6)
% 3.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ r2_hidden(X0,X2)
% 3.96/1.00      | r2_hidden(X1,X2) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_854]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_10,plain,
% 3.96/1.00      ( m1_subset_1(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ r2_hidden(X0,X2) ),
% 3.96/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_871,plain,
% 3.96/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ v13_waybel_0(X2,sK6)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ r2_hidden(X0,X2)
% 3.96/1.00      | r2_hidden(X1,X2) ),
% 3.96/1.00      inference(forward_subsumption_resolution,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_855,c_10]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2589,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.96/1.00      | v13_waybel_0(X2,sK6) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.96/1.00      | r2_hidden(X1,X2) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_871]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4372,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.96/1.00      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.96/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2605,c_2589]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_36,negated_conjecture,
% 3.96/1.00      ( v13_waybel_0(sK7,sK6) ),
% 3.96/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1031,plain,
% 3.96/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ r2_hidden(X0,X2)
% 3.96/1.00      | r2_hidden(X1,X2)
% 3.96/1.00      | sK7 != X2
% 3.96/1.00      | sK6 != sK6 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_36,c_871]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1032,plain,
% 3.96/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ r2_hidden(X0,sK7)
% 3.96/1.00      | r2_hidden(X1,sK7) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_1031]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1034,plain,
% 3.96/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ r2_hidden(X0,sK7)
% 3.96/1.00      | r2_hidden(X1,sK7) ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_1032,c_35]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1035,plain,
% 3.96/1.00      ( ~ r1_orders_2(sK6,X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.96/1.00      | ~ r2_hidden(X0,sK7)
% 3.96/1.00      | r2_hidden(X1,sK7) ),
% 3.96/1.00      inference(renaming,[status(thm)],[c_1034]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1036,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.96/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4959,plain,
% 3.96/1.00      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) != iProver_top
% 3.96/1.00      | r2_hidden(X1,sK7) = iProver_top ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_4372,c_1036]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_9276,plain,
% 3.96/1.00      ( r2_lattice3(sK6,X0,X1) != iProver_top
% 3.96/1.00      | r2_lattice3(sK6,X0,X2) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X1,sK7) = iProver_top
% 3.96/1.00      | r2_hidden(sK2(sK6,X0,X2),sK7) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_8377,c_4959]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_11576,plain,
% 3.96/1.00      ( r2_lattice3(sK6,sK7,X0) != iProver_top
% 3.96/1.00      | r2_lattice3(sK6,sK7,X1) = iProver_top
% 3.96/1.00      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) = iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2583,c_9276]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_45,plain,
% 3.96/1.00      ( l1_orders_2(sK6) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_23,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_76,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 3.96/1.00      | l1_orders_2(X0) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_78,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
% 3.96/1.00      | l1_orders_2(sK6) != iProver_top ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_76]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2037,plain,
% 3.96/1.00      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.96/1.00      theory(equality) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2051,plain,
% 3.96/1.00      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2037]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2027,plain,( X0 = X0 ),theory(equality) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2058,plain,
% 3.96/1.00      ( sK6 = sK6 ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3113,plain,
% 3.96/1.00      ( sK7 = sK7 ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2028,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3080,plain,
% 3.96/1.00      ( u1_struct_0(sK6) != X0 | sK7 != X0 | sK7 = u1_struct_0(sK6) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2028]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3597,plain,
% 3.96/1.00      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3080]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_20,plain,
% 3.96/1.00      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.96/1.00      | ~ r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ r1_yellow_0(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_22,plain,
% 3.96/1.00      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_258,plain,
% 3.96/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ r1_yellow_0(X0,X1)
% 3.96/1.00      | ~ r2_lattice3(X0,X1,X2)
% 3.96/1.00      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_20,c_22]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_259,plain,
% 3.96/1.00      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.96/1.00      | ~ r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ r1_yellow_0(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(renaming,[status(thm)],[c_258]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_24,plain,
% 3.96/1.00      ( r1_yellow_0(X0,k1_xboole_0)
% 3.96/1.00      | v2_struct_0(X0)
% 3.96/1.00      | ~ v5_orders_2(X0)
% 3.96/1.00      | ~ v1_yellow_0(X0)
% 3.96/1.00      | ~ l1_orders_2(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_39,negated_conjecture,
% 3.96/1.00      ( v1_yellow_0(sK6) ),
% 3.96/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_594,plain,
% 3.96/1.00      ( r1_yellow_0(X0,k1_xboole_0)
% 3.96/1.00      | v2_struct_0(X0)
% 3.96/1.00      | ~ v5_orders_2(X0)
% 3.96/1.00      | ~ l1_orders_2(X0)
% 3.96/1.00      | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_595,plain,
% 3.96/1.00      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.96/1.00      | v2_struct_0(sK6)
% 3.96/1.00      | ~ v5_orders_2(sK6)
% 3.96/1.00      | ~ l1_orders_2(sK6) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_594]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_41,negated_conjecture,
% 3.96/1.00      ( ~ v2_struct_0(sK6) ),
% 3.96/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_40,negated_conjecture,
% 3.96/1.00      ( v5_orders_2(sK6) ),
% 3.96/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_74,plain,
% 3.96/1.00      ( r1_yellow_0(sK6,k1_xboole_0)
% 3.96/1.00      | v2_struct_0(sK6)
% 3.96/1.00      | ~ v5_orders_2(sK6)
% 3.96/1.00      | ~ v1_yellow_0(sK6)
% 3.96/1.00      | ~ l1_orders_2(sK6) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_597,plain,
% 3.96/1.00      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_595,c_41,c_40,c_39,c_38,c_74]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_693,plain,
% 3.96/1.00      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.96/1.00      | ~ r2_lattice3(X0,X1,X2)
% 3.96/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.96/1.00      | ~ l1_orders_2(X0)
% 3.96/1.00      | sK6 != X0
% 3.96/1.00      | k1_xboole_0 != X1 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_259,c_597]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_694,plain,
% 3.96/1.00      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.96/1.00      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.96/1.00      | ~ l1_orders_2(sK6) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_693]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_698,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.96/1.00      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.96/1.00      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_694,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_699,plain,
% 3.96/1.00      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.96/1.00      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.96/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.96/1.00      inference(renaming,[status(thm)],[c_698]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2597,plain,
% 3.96/1.00      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 3.96/1.00      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_16,plain,
% 3.96/1.00      ( ~ l1_orders_2(X0)
% 3.96/1.00      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_910,plain,
% 3.96/1.00      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_911,plain,
% 3.96/1.00      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_910]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2707,plain,
% 3.96/1.00      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.96/1.00      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.96/1.00      inference(light_normalisation,[status(thm)],[c_2597,c_911]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4968,plain,
% 3.96/1.00      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) = iProver_top
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2707,c_4959]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_8,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.96/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_37,negated_conjecture,
% 3.96/1.00      ( ~ v1_xboole_0(sK7) ),
% 3.96/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_565,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK7 != X1 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_37]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_566,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5207,plain,
% 3.96/1.00      ( ~ m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_566]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5208,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(sK6),sK7) != iProver_top
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_5207]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_31,plain,
% 3.96/1.00      ( v1_subset_1(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | X0 = X1 ),
% 3.96/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_33,negated_conjecture,
% 3.96/1.00      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.96/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_337,plain,
% 3.96/1.00      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.96/1.00      inference(prop_impl,[status(thm)],[c_33]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_631,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | X1 = X0
% 3.96/1.00      | u1_struct_0(sK6) != X1
% 3.96/1.00      | sK7 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_337]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_632,plain,
% 3.96/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | u1_struct_0(sK6) = sK7 ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_631]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_634,plain,
% 3.96/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_632,c_35]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2600,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = sK7
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5415,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = sK7
% 3.96/1.00      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) = iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2600,c_4968]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_1,plain,
% 3.96/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.96/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2612,plain,
% 3.96/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_9,plain,
% 3.96/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.96/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_11,plain,
% 3.96/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_580,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 3.96/1.00      inference(resolution,[status(thm)],[c_9,c_11]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2602,plain,
% 3.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4863,plain,
% 3.96/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2612,c_2602]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5704,plain,
% 3.96/1.00      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 3.96/1.00      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2583,c_4863]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2031,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.96/1.00      theory(equality) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3025,plain,
% 3.96/1.00      ( m1_subset_1(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.96/1.00      | X0 != k3_yellow_0(sK6)
% 3.96/1.00      | X1 != u1_struct_0(sK6) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3334,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(sK6),X0)
% 3.96/1.00      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.96/1.00      | X0 != u1_struct_0(sK6)
% 3.96/1.00      | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3025]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7012,plain,
% 3.96/1.00      ( ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.96/1.00      | m1_subset_1(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.96/1.00      | sK7 != u1_struct_0(sK6) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3334]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7015,plain,
% 3.96/1.00      ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 3.96/1.00      | sK7 != u1_struct_0(sK6)
% 3.96/1.00      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | m1_subset_1(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_7012]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_11622,plain,
% 3.96/1.00      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) = iProver_top ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_11576,c_45,c_78,c_2051,c_2058,c_3113,c_3597,c_4968,
% 3.96/1.00                 c_5208,c_5415,c_5704,c_7015]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_11631,plain,
% 3.96/1.00      ( X0 = X1
% 3.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(u1_struct_0(sK6),X1,X0),sK7) = iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2609,c_11622]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_0,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ r2_hidden(X2,X0)
% 3.96/1.00      | r2_hidden(X2,X1) ),
% 3.96/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2613,plain,
% 3.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.96/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3270,plain,
% 3.96/1.00      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 3.96/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2605,c_2613]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.96/1.00      | ~ r2_hidden(sK0(X1,X0,X2),X0)
% 3.96/1.00      | X0 = X2 ),
% 3.96/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2611,plain,
% 3.96/1.00      ( X0 = X1
% 3.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.96/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3964,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = X0
% 3.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X1)) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),X0) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(X1,X0,u1_struct_0(sK6)),sK7) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_3270,c_2611]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_15959,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = sK7
% 3.96/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | r2_hidden(sK0(u1_struct_0(sK6),sK7,u1_struct_0(sK6)),sK7) != iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_11631,c_3964]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_16003,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = sK7
% 3.96/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.96/1.00      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.96/1.00      inference(forward_subsumption_resolution,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_15959,c_11631]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_894,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK6 != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_895,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_894]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2587,plain,
% 3.96/1.00      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_895]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_11630,plain,
% 3.96/1.00      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.96/1.00      inference(superposition,[status(thm)],[c_2587,c_11622]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3015,plain,
% 3.96/1.00      ( m1_subset_1(X0,X1)
% 3.96/1.00      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 3.96/1.00      | X0 != sK1(X2)
% 3.96/1.00      | X1 != k1_zfmisc_1(X2) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3172,plain,
% 3.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 3.96/1.00      | X0 != sK1(X1)
% 3.96/1.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3015]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5305,plain,
% 3.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | X0 != sK1(u1_struct_0(sK6))
% 3.96/1.00      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3172]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7804,plain,
% 3.96/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | ~ m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.96/1.00      | u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
% 3.96/1.00      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_5305]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_7806,plain,
% 3.96/1.00      ( u1_struct_0(sK6) != sK1(u1_struct_0(sK6))
% 3.96/1.00      | k1_zfmisc_1(u1_struct_0(sK6)) != k1_zfmisc_1(u1_struct_0(sK6))
% 3.96/1.00      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.96/1.00      | m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_7804]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_5,plain,
% 3.96/1.00      ( ~ v1_subset_1(sK1(X0),X0) ),
% 3.96/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_608,plain,
% 3.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/1.00      | X1 != X2
% 3.96/1.00      | X1 = X0
% 3.96/1.00      | sK1(X2) != X0 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_31]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_609,plain,
% 3.96/1.00      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_608]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_6,plain,
% 3.96/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.96/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_613,plain,
% 3.96/1.00      ( X0 = sK1(X0) ),
% 3.96/1.00      inference(global_propositional_subsumption,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_609,c_6]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4550,plain,
% 3.96/1.00      ( u1_struct_0(sK6) = sK1(u1_struct_0(sK6)) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_613]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_3173,plain,
% 3.96/1.00      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_4010,plain,
% 3.96/1.00      ( k1_zfmisc_1(u1_struct_0(sK6)) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_3173]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2966,plain,
% 3.96/1.00      ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.96/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2972,plain,
% 3.96/1.00      ( m1_subset_1(sK1(u1_struct_0(sK6)),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2966]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_34,negated_conjecture,
% 3.96/1.00      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.96/1.00      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.96/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_335,plain,
% 3.96/1.00      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.96/1.00      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.96/1.00      inference(prop_impl,[status(thm)],[c_34]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_619,plain,
% 3.96/1.00      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | u1_struct_0(sK6) != X0
% 3.96/1.00      | sK1(X0) != sK7 ),
% 3.96/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_335]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_620,plain,
% 3.96/1.00      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.96/1.00      | sK1(u1_struct_0(sK6)) != sK7 ),
% 3.96/1.00      inference(unflattening,[status(thm)],[c_619]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2601,plain,
% 3.96/1.00      ( sK1(u1_struct_0(sK6)) != sK7
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_2646,plain,
% 3.96/1.00      ( u1_struct_0(sK6) != sK7
% 3.96/1.00      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.96/1.00      inference(demodulation,[status(thm)],[c_2601,c_613]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(c_48,plain,
% 3.96/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.96/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.96/1.00  
% 3.96/1.00  cnf(contradiction,plain,
% 3.96/1.00      ( $false ),
% 3.96/1.00      inference(minisat,
% 3.96/1.00                [status(thm)],
% 3.96/1.00                [c_16003,c_11630,c_7806,c_4550,c_4010,c_2972,c_2646,c_48]) ).
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/1.00  
% 3.96/1.00  ------                               Statistics
% 3.96/1.00  
% 3.96/1.00  ------ General
% 3.96/1.00  
% 3.96/1.00  abstr_ref_over_cycles:                  0
% 3.96/1.00  abstr_ref_under_cycles:                 0
% 3.96/1.00  gc_basic_clause_elim:                   0
% 3.96/1.00  forced_gc_time:                         0
% 3.96/1.00  parsing_time:                           0.016
% 3.96/1.00  unif_index_cands_time:                  0.
% 3.96/1.00  unif_index_add_time:                    0.
% 3.96/1.00  orderings_time:                         0.
% 3.96/1.00  out_proof_time:                         0.013
% 3.96/1.00  total_time:                             0.454
% 3.96/1.00  num_of_symbols:                         57
% 3.96/1.00  num_of_terms:                           15052
% 3.96/1.00  
% 3.96/1.00  ------ Preprocessing
% 3.96/1.00  
% 3.96/1.00  num_of_splits:                          0
% 3.96/1.00  num_of_split_atoms:                     0
% 3.96/1.00  num_of_reused_defs:                     0
% 3.96/1.00  num_eq_ax_congr_red:                    37
% 3.96/1.00  num_of_sem_filtered_clauses:            1
% 3.96/1.00  num_of_subtypes:                        0
% 3.96/1.00  monotx_restored_types:                  0
% 3.96/1.00  sat_num_of_epr_types:                   0
% 3.96/1.00  sat_num_of_non_cyclic_types:            0
% 3.96/1.00  sat_guarded_non_collapsed_types:        0
% 3.96/1.00  num_pure_diseq_elim:                    0
% 3.96/1.00  simp_replaced_by:                       0
% 3.96/1.00  res_preprocessed:                       177
% 3.96/1.00  prep_upred:                             0
% 3.96/1.00  prep_unflattend:                        71
% 3.96/1.00  smt_new_axioms:                         0
% 3.96/1.00  pred_elim_cands:                        5
% 3.96/1.00  pred_elim:                              8
% 3.96/1.00  pred_elim_cl:                           8
% 3.96/1.00  pred_elim_cycles:                       12
% 3.96/1.00  merged_defs:                            2
% 3.96/1.00  merged_defs_ncl:                        0
% 3.96/1.00  bin_hyper_res:                          2
% 3.96/1.00  prep_cycles:                            4
% 3.96/1.00  pred_elim_time:                         0.025
% 3.96/1.00  splitting_time:                         0.
% 3.96/1.00  sem_filter_time:                        0.
% 3.96/1.00  monotx_time:                            0.
% 3.96/1.00  subtype_inf_time:                       0.
% 3.96/1.00  
% 3.96/1.00  ------ Problem properties
% 3.96/1.00  
% 3.96/1.00  clauses:                                34
% 3.96/1.00  conjectures:                            2
% 3.96/1.00  epr:                                    3
% 3.96/1.00  horn:                                   23
% 3.96/1.00  ground:                                 8
% 3.96/1.00  unary:                                  9
% 3.96/1.00  binary:                                 5
% 3.96/1.00  lits:                                   92
% 3.96/1.00  lits_eq:                                11
% 3.96/1.00  fd_pure:                                0
% 3.96/1.00  fd_pseudo:                              0
% 3.96/1.00  fd_cond:                                3
% 3.96/1.00  fd_pseudo_cond:                         3
% 3.96/1.00  ac_symbols:                             0
% 3.96/1.00  
% 3.96/1.00  ------ Propositional Solver
% 3.96/1.00  
% 3.96/1.00  prop_solver_calls:                      28
% 3.96/1.00  prop_fast_solver_calls:                 1850
% 3.96/1.00  smt_solver_calls:                       0
% 3.96/1.00  smt_fast_solver_calls:                  0
% 3.96/1.00  prop_num_of_clauses:                    5273
% 3.96/1.00  prop_preprocess_simplified:             12079
% 3.96/1.00  prop_fo_subsumed:                       36
% 3.96/1.00  prop_solver_time:                       0.
% 3.96/1.00  smt_solver_time:                        0.
% 3.96/1.00  smt_fast_solver_time:                   0.
% 3.96/1.00  prop_fast_solver_time:                  0.
% 3.96/1.00  prop_unsat_core_time:                   0.
% 3.96/1.00  
% 3.96/1.00  ------ QBF
% 3.96/1.00  
% 3.96/1.00  qbf_q_res:                              0
% 3.96/1.00  qbf_num_tautologies:                    0
% 3.96/1.00  qbf_prep_cycles:                        0
% 3.96/1.00  
% 3.96/1.00  ------ BMC1
% 3.96/1.00  
% 3.96/1.00  bmc1_current_bound:                     -1
% 3.96/1.00  bmc1_last_solved_bound:                 -1
% 3.96/1.00  bmc1_unsat_core_size:                   -1
% 3.96/1.00  bmc1_unsat_core_parents_size:           -1
% 3.96/1.00  bmc1_merge_next_fun:                    0
% 3.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.96/1.00  
% 3.96/1.00  ------ Instantiation
% 3.96/1.00  
% 3.96/1.00  inst_num_of_clauses:                    1297
% 3.96/1.00  inst_num_in_passive:                    342
% 3.96/1.00  inst_num_in_active:                     536
% 3.96/1.00  inst_num_in_unprocessed:                419
% 3.96/1.00  inst_num_of_loops:                      680
% 3.96/1.00  inst_num_of_learning_restarts:          0
% 3.96/1.00  inst_num_moves_active_passive:          141
% 3.96/1.00  inst_lit_activity:                      0
% 3.96/1.00  inst_lit_activity_moves:                0
% 3.96/1.00  inst_num_tautologies:                   0
% 3.96/1.00  inst_num_prop_implied:                  0
% 3.96/1.00  inst_num_existing_simplified:           0
% 3.96/1.00  inst_num_eq_res_simplified:             0
% 3.96/1.00  inst_num_child_elim:                    0
% 3.96/1.00  inst_num_of_dismatching_blockings:      647
% 3.96/1.00  inst_num_of_non_proper_insts:           1239
% 3.96/1.00  inst_num_of_duplicates:                 0
% 3.96/1.00  inst_inst_num_from_inst_to_res:         0
% 3.96/1.00  inst_dismatching_checking_time:         0.
% 3.96/1.00  
% 3.96/1.00  ------ Resolution
% 3.96/1.00  
% 3.96/1.00  res_num_of_clauses:                     0
% 3.96/1.00  res_num_in_passive:                     0
% 3.96/1.00  res_num_in_active:                      0
% 3.96/1.00  res_num_of_loops:                       181
% 3.96/1.00  res_forward_subset_subsumed:            211
% 3.96/1.00  res_backward_subset_subsumed:           0
% 3.96/1.00  res_forward_subsumed:                   0
% 3.96/1.00  res_backward_subsumed:                  0
% 3.96/1.00  res_forward_subsumption_resolution:     6
% 3.96/1.00  res_backward_subsumption_resolution:    0
% 3.96/1.00  res_clause_to_clause_subsumption:       2436
% 3.96/1.00  res_orphan_elimination:                 0
% 3.96/1.00  res_tautology_del:                      75
% 3.96/1.00  res_num_eq_res_simplified:              0
% 3.96/1.00  res_num_sel_changes:                    0
% 3.96/1.00  res_moves_from_active_to_pass:          0
% 3.96/1.00  
% 3.96/1.00  ------ Superposition
% 3.96/1.00  
% 3.96/1.00  sup_time_total:                         0.
% 3.96/1.00  sup_time_generating:                    0.
% 3.96/1.00  sup_time_sim_full:                      0.
% 3.96/1.00  sup_time_sim_immed:                     0.
% 3.96/1.00  
% 3.96/1.00  sup_num_of_clauses:                     330
% 3.96/1.00  sup_num_in_active:                      134
% 3.96/1.00  sup_num_in_passive:                     196
% 3.96/1.00  sup_num_of_loops:                       134
% 3.96/1.00  sup_fw_superposition:                   214
% 3.96/1.00  sup_bw_superposition:                   202
% 3.96/1.00  sup_immediate_simplified:               69
% 3.96/1.00  sup_given_eliminated:                   1
% 3.96/1.00  comparisons_done:                       0
% 3.96/1.00  comparisons_avoided:                    0
% 3.96/1.00  
% 3.96/1.00  ------ Simplifications
% 3.96/1.00  
% 3.96/1.00  
% 3.96/1.00  sim_fw_subset_subsumed:                 23
% 3.96/1.00  sim_bw_subset_subsumed:                 10
% 3.96/1.00  sim_fw_subsumed:                        30
% 3.96/1.00  sim_bw_subsumed:                        9
% 3.96/1.00  sim_fw_subsumption_res:                 5
% 3.96/1.00  sim_bw_subsumption_res:                 1
% 3.96/1.00  sim_tautology_del:                      5
% 3.96/1.00  sim_eq_tautology_del:                   13
% 3.96/1.00  sim_eq_res_simp:                        0
% 3.96/1.00  sim_fw_demodulated:                     4
% 3.96/1.00  sim_bw_demodulated:                     0
% 3.96/1.00  sim_light_normalised:                   6
% 3.96/1.00  sim_joinable_taut:                      0
% 3.96/1.00  sim_joinable_simp:                      0
% 3.96/1.00  sim_ac_normalised:                      0
% 3.96/1.00  sim_smt_subsumption:                    0
% 3.96/1.00  
%------------------------------------------------------------------------------
