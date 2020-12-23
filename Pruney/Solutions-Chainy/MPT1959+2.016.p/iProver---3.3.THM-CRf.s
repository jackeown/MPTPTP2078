%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:27 EST 2020

% Result     : Theorem 35.86s
% Output     : CNFRefutation 35.86s
% Verified   : 
% Statistics : Number of formulae       :  294 (4414 expanded)
%              Number of clauses        :  175 ( 891 expanded)
%              Number of leaves         :   30 ( 849 expanded)
%              Depth                    :   29
%              Number of atoms          : 1277 (37262 expanded)
%              Number of equality atoms :  286 (1038 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f69,plain,(
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
    inference(rectify,[],[f68])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r1_orders_2(X0,X2,sK7(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
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
            & r1_orders_2(X0,sK6(X0,X1),X3)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK7(X0,X1),X1)
                & r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f69,f71,f70])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f18])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

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
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

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
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( r2_hidden(k3_yellow_0(X0),sK9)
          | ~ v1_subset_1(sK9,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK9)
          | v1_subset_1(sK9,u1_struct_0(X0)) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK9,X0)
        & ~ v1_xboole_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
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
          ( ( r2_hidden(k3_yellow_0(sK8),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK8)) )
          & ( ~ r2_hidden(k3_yellow_0(sK8),X1)
            | v1_subset_1(X1,u1_struct_0(sK8)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & v13_waybel_0(X1,sK8)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK8)
      & v1_yellow_0(sK8)
      & v5_orders_2(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( r2_hidden(k3_yellow_0(sK8),sK9)
      | ~ v1_subset_1(sK9,u1_struct_0(sK8)) )
    & ( ~ r2_hidden(k3_yellow_0(sK8),sK9)
      | v1_subset_1(sK9,u1_struct_0(sK8)) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v13_waybel_0(sK9,sK8)
    & ~ v1_xboole_0(sK9)
    & l1_orders_2(sK8)
    & v1_yellow_0(sK8)
    & v5_orders_2(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f75,f77,f76])).

fof(f122,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

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

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f78])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f117,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f132,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f117])).

fof(f126,plain,
    ( ~ r2_hidden(k3_yellow_0(sK8),sK9)
    | v1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f78])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f103,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    v13_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f123,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f78])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f110,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f121,plain,(
    v1_yellow_0(sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f119,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f120,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f127,plain,
    ( r2_hidden(k3_yellow_0(sK8),sK9)
    | ~ v1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f78])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
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

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f25])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
          | ~ r2_hidden(sK3(X0,X1,X2),X1) )
        & ( r2_hidden(sK3(X0,X1,X2),X2)
          | r2_hidden(sK3(X0,X1,X2),X1) )
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) )
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3437,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3437,c_14])).

cnf(c_34,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK6(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_45,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1148,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK6(X1,X0),X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_45])).

cnf(c_1149,plain,
    ( v13_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK6(sK8,X0),X0) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_3412,plain,
    ( v13_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK6(sK8,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_3983,plain,
    ( v13_waybel_0(u1_struct_0(sK8),sK8) = iProver_top
    | r2_hidden(sK6(sK8,u1_struct_0(sK8)),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_3412])).

cnf(c_36,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1118,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_45])).

cnf(c_1119,plain,
    ( v13_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1118])).

cnf(c_3414,plain,
    ( v13_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_23,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1052,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_45])).

cnf(c_1053,plain,
    ( r1_orders_2(sK8,X0,X1)
    | ~ r2_lattice3(sK8,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1052])).

cnf(c_3418,plain,
    ( r1_orders_2(sK8,X0,X1) = iProver_top
    | r2_lattice3(sK8,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_4566,plain,
    ( r1_orders_2(sK8,sK6(sK8,X0),X1) = iProver_top
    | r2_lattice3(sK8,X2,X1) != iProver_top
    | v13_waybel_0(X0,sK8) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK6(sK8,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3414,c_3418])).

cnf(c_11715,plain,
    ( r1_orders_2(sK8,sK6(sK8,u1_struct_0(sK8)),X0) = iProver_top
    | r2_lattice3(sK8,u1_struct_0(sK8),X0) != iProver_top
    | v13_waybel_0(u1_struct_0(sK8),sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_4566])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_55,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_41,negated_conjecture,
    ( v1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(k3_yellow_0(sK8),sK9) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_394,plain,
    ( v1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(k3_yellow_0(sK8),sK9) ),
    inference(prop_impl,[status(thm)],[c_41])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK8),sK9)
    | u1_struct_0(sK8) != X0
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_394])).

cnf(c_687,plain,
    ( ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(k3_yellow_0(sK8),sK9)
    | sK9 != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_3427,plain,
    ( sK9 != u1_struct_0(sK8)
    | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_3578,plain,
    ( u1_struct_0(sK8) != sK9
    | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3427,c_3463])).

cnf(c_24,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1047,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_45])).

cnf(c_1048,plain,
    ( k1_yellow_0(sK8,k1_xboole_0) = k3_yellow_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1047])).

cnf(c_30,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1038,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_45])).

cnf(c_1039,plain,
    ( m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1038])).

cnf(c_3419,plain,
    ( m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_3858,plain,
    ( m1_subset_1(k3_yellow_0(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_3419])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3447,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_1])).

cnf(c_313,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_3429,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_7695,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3429])).

cnf(c_11924,plain,
    ( r1_orders_2(sK8,sK1(u1_struct_0(sK8),X0),X1) = iProver_top
    | r2_lattice3(sK8,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(sK8),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK8),X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7695,c_3418])).

cnf(c_14683,plain,
    ( r1_orders_2(sK8,sK1(u1_struct_0(sK8),X0),X1) = iProver_top
    | r2_lattice3(sK8,u1_struct_0(sK8),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(sK8),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_11924])).

cnf(c_3432,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_37,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_998,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_45])).

cnf(c_999,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ v13_waybel_0(X2,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_19,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1015,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ v13_waybel_0(X2,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_999,c_19])).

cnf(c_3421,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_5389,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | v13_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_3421])).

cnf(c_43,negated_conjecture,
    ( v13_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1226,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK9 != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_1015])).

cnf(c_1227,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,sK9)
    | r2_hidden(X1,sK9) ),
    inference(unflattening,[status(thm)],[c_1226])).

cnf(c_1228,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_5990,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5389,c_55,c_1228])).

cnf(c_142418,plain,
    ( r2_lattice3(sK8,u1_struct_0(sK8),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(sK8),X1) = iProver_top
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK8),X1),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_14683,c_5990])).

cnf(c_52,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_53,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_54,plain,
    ( v13_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_154,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_28,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_30])).

cnf(c_292,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_31,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_46,negated_conjecture,
    ( v1_yellow_0(sK8) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_656,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_46])).

cnf(c_657,plain,
    ( r1_yellow_0(sK8,k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v5_orders_2(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_47,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_81,plain,
    ( r1_yellow_0(sK8,k1_xboole_0)
    | v2_struct_0(sK8)
    | ~ v5_orders_2(sK8)
    | ~ v1_yellow_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_659,plain,
    ( r1_yellow_0(sK8,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_48,c_47,c_46,c_45,c_81])).

cnf(c_730,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_292,c_659])).

cnf(c_731,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_732,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_29,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_284,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_30])).

cnf(c_285,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_751,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK8 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_285,c_659])).

cnf(c_752,plain,
    ( r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_27,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_762,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK8 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_659])).

cnf(c_763,plain,
    ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_767,plain,
    ( m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_45])).

cnf(c_768,plain,
    ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(renaming,[status(thm)],[c_767])).

cnf(c_3812,plain,
    ( ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
    | m1_subset_1(sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)),u1_struct_0(sK8))
    | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_26,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK5(X0,X1,X2))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_786,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X1,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X1) = X2
    | sK8 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_659])).

cnf(c_787,plain,
    ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_45])).

cnf(c_792,plain,
    ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_3815,plain,
    ( r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
    | ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
    | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_25,plain,
    ( ~ r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ r1_yellow_0(X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = X1 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_706,plain,
    ( ~ r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,X2) = X1
    | sK8 != X0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_659])).

cnf(c_707,plain,
    ( ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8)
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_45])).

cnf(c_712,plain,
    ( ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
    inference(renaming,[status(thm)],[c_711])).

cnf(c_3818,plain,
    ( ~ r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
    | ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
    | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
    | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_2503,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4095,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_4732,plain,
    ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_4733,plain,
    ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4732])).

cnf(c_2504,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3972,plain,
    ( u1_struct_0(sK8) != X0
    | sK9 != X0
    | sK9 = u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_4804,plain,
    ( u1_struct_0(sK8) != sK9
    | sK9 = u1_struct_0(sK8)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_3972])).

cnf(c_38,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_40,negated_conjecture,
    ( ~ v1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(k3_yellow_0(sK8),sK9) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_396,plain,
    ( ~ v1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(k3_yellow_0(sK8),sK9) ),
    inference(prop_impl,[status(thm)],[c_40])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK8),sK9)
    | X1 = X0
    | u1_struct_0(sK8) != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_396])).

cnf(c_673,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(k3_yellow_0(sK8),sK9)
    | u1_struct_0(sK8) = sK9 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_675,plain,
    ( r2_hidden(k3_yellow_0(sK8),sK9)
    | u1_struct_0(sK8) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_42])).

cnf(c_3428,plain,
    ( u1_struct_0(sK8) = sK9
    | r2_hidden(k3_yellow_0(sK8),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_45])).

cnf(c_736,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
    | ~ r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_3425,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_3587,plain,
    ( r1_orders_2(sK8,k3_yellow_0(sK8),X0) = iProver_top
    | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3425,c_1048])).

cnf(c_5999,plain,
    ( r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3587,c_5990])).

cnf(c_6448,plain,
    ( u1_struct_0(sK8) = sK9
    | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3428,c_5999])).

cnf(c_9165,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
    | ~ r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
    | ~ m1_subset_1(sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_3821,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ v13_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,sK9)
    | r2_hidden(X1,sK9) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_65030,plain,
    ( ~ r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
    | ~ v13_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X0,sK9)
    | ~ r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) ),
    inference(instantiation,[status(thm)],[c_3821])).

cnf(c_65031,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) != iProver_top
    | v13_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top
    | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65030])).

cnf(c_2509,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4051,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,sK9)
    | X2 != X0
    | sK9 != X1 ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_5219,plain,
    ( m1_subset_1(X0,sK9)
    | ~ m1_subset_1(k1_yellow_0(sK8,X1),u1_struct_0(sK8))
    | X0 != k1_yellow_0(sK8,X1)
    | sK9 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_10410,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8))
    | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
    | k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,X0)
    | sK9 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_5219])).

cnf(c_89531,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
    | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
    | k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,k1_xboole_0)
    | sK9 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_10410])).

cnf(c_89532,plain,
    ( k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,k1_xboole_0)
    | sK9 != u1_struct_0(sK8)
    | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89531])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3892,plain,
    ( ~ m1_subset_1(X0,sK9)
    | r2_hidden(X0,sK9)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_108550,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
    | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_3892])).

cnf(c_108551,plain,
    ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108550])).

cnf(c_133020,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_134909,plain,
    ( ~ r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_133020])).

cnf(c_134911,plain,
    ( r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134909])).

cnf(c_21,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1088,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_45])).

cnf(c_1089,plain,
    ( r2_lattice3(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(sK4(sK8,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1088])).

cnf(c_134910,plain,
    ( r2_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_134915,plain,
    ( r2_lattice3(sK8,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134910])).

cnf(c_145104,plain,
    ( r2_hidden(X0,sK9) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_142418,c_45,c_52,c_53,c_54,c_55,c_154,c_732,c_752,c_3812,c_3815,c_3818,c_4095,c_4732,c_4733,c_4804,c_6448,c_9165,c_65031,c_89532,c_108551,c_134911,c_134915])).

cnf(c_145105,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_145104])).

cnf(c_145120,plain,
    ( r2_hidden(k3_yellow_0(sK8),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3858,c_145105])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK3(X1,X2,X0),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3434,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK3(X2,X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_145113,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK3(u1_struct_0(sK8),X1,X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_145105])).

cnf(c_3438,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5529,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_3438])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3871,plain,
    ( ~ m1_subset_1(sK9,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4015,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_3871])).

cnf(c_4016,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4015])).

cnf(c_4126,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5044,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4126])).

cnf(c_5045,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5044])).

cnf(c_6026,plain,
    ( r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5529,c_53,c_55,c_4016,c_5045])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_3441,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6032,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6026,c_3441])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3446,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6649,plain,
    ( r2_hidden(X0,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6032,c_3446])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK3(X1,X2,X0),X0)
    | ~ r2_hidden(sK3(X1,X2,X0),X2)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3436,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK3(X2,X0,X1),X1) != iProver_top
    | r2_hidden(sK3(X2,X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10917,plain,
    ( u1_struct_0(sK8) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0,u1_struct_0(sK8)),X0) != iProver_top
    | r2_hidden(sK3(X1,X0,u1_struct_0(sK8)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6649,c_3436])).

cnf(c_147636,plain,
    ( u1_struct_0(sK8) = sK9
    | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK3(u1_struct_0(sK8),sK9,u1_struct_0(sK8)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_145113,c_10917])).

cnf(c_147671,plain,
    ( u1_struct_0(sK8) = sK9
    | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_147636,c_145113])).

cnf(c_179567,plain,
    ( m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11715,c_55,c_3578,c_145120,c_147671])).

cnf(c_179572,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_179567,c_3463])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:11:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.86/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.86/4.98  
% 35.86/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.86/4.98  
% 35.86/4.98  ------  iProver source info
% 35.86/4.98  
% 35.86/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.86/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.86/4.98  git: non_committed_changes: false
% 35.86/4.98  git: last_make_outside_of_git: false
% 35.86/4.98  
% 35.86/4.98  ------ 
% 35.86/4.98  
% 35.86/4.98  ------ Input Options
% 35.86/4.98  
% 35.86/4.98  --out_options                           all
% 35.86/4.98  --tptp_safe_out                         true
% 35.86/4.98  --problem_path                          ""
% 35.86/4.98  --include_path                          ""
% 35.86/4.98  --clausifier                            res/vclausify_rel
% 35.86/4.98  --clausifier_options                    --mode clausify
% 35.86/4.98  --stdin                                 false
% 35.86/4.98  --stats_out                             all
% 35.86/4.98  
% 35.86/4.98  ------ General Options
% 35.86/4.98  
% 35.86/4.98  --fof                                   false
% 35.86/4.98  --time_out_real                         305.
% 35.86/4.98  --time_out_virtual                      -1.
% 35.86/4.98  --symbol_type_check                     false
% 35.86/4.98  --clausify_out                          false
% 35.86/4.98  --sig_cnt_out                           false
% 35.86/4.98  --trig_cnt_out                          false
% 35.86/4.98  --trig_cnt_out_tolerance                1.
% 35.86/4.98  --trig_cnt_out_sk_spl                   false
% 35.86/4.98  --abstr_cl_out                          false
% 35.86/4.98  
% 35.86/4.98  ------ Global Options
% 35.86/4.98  
% 35.86/4.98  --schedule                              default
% 35.86/4.98  --add_important_lit                     false
% 35.86/4.98  --prop_solver_per_cl                    1000
% 35.86/4.98  --min_unsat_core                        false
% 35.86/4.98  --soft_assumptions                      false
% 35.86/4.98  --soft_lemma_size                       3
% 35.86/4.98  --prop_impl_unit_size                   0
% 35.86/4.98  --prop_impl_unit                        []
% 35.86/4.98  --share_sel_clauses                     true
% 35.86/4.98  --reset_solvers                         false
% 35.86/4.98  --bc_imp_inh                            [conj_cone]
% 35.86/4.98  --conj_cone_tolerance                   3.
% 35.86/4.98  --extra_neg_conj                        none
% 35.86/4.98  --large_theory_mode                     true
% 35.86/4.98  --prolific_symb_bound                   200
% 35.86/4.98  --lt_threshold                          2000
% 35.86/4.98  --clause_weak_htbl                      true
% 35.86/4.98  --gc_record_bc_elim                     false
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing Options
% 35.86/4.98  
% 35.86/4.98  --preprocessing_flag                    true
% 35.86/4.98  --time_out_prep_mult                    0.1
% 35.86/4.98  --splitting_mode                        input
% 35.86/4.98  --splitting_grd                         true
% 35.86/4.98  --splitting_cvd                         false
% 35.86/4.98  --splitting_cvd_svl                     false
% 35.86/4.98  --splitting_nvd                         32
% 35.86/4.98  --sub_typing                            true
% 35.86/4.98  --prep_gs_sim                           true
% 35.86/4.98  --prep_unflatten                        true
% 35.86/4.98  --prep_res_sim                          true
% 35.86/4.98  --prep_upred                            true
% 35.86/4.98  --prep_sem_filter                       exhaustive
% 35.86/4.98  --prep_sem_filter_out                   false
% 35.86/4.98  --pred_elim                             true
% 35.86/4.98  --res_sim_input                         true
% 35.86/4.98  --eq_ax_congr_red                       true
% 35.86/4.98  --pure_diseq_elim                       true
% 35.86/4.98  --brand_transform                       false
% 35.86/4.98  --non_eq_to_eq                          false
% 35.86/4.98  --prep_def_merge                        true
% 35.86/4.98  --prep_def_merge_prop_impl              false
% 35.86/4.98  --prep_def_merge_mbd                    true
% 35.86/4.98  --prep_def_merge_tr_red                 false
% 35.86/4.98  --prep_def_merge_tr_cl                  false
% 35.86/4.98  --smt_preprocessing                     true
% 35.86/4.98  --smt_ac_axioms                         fast
% 35.86/4.98  --preprocessed_out                      false
% 35.86/4.98  --preprocessed_stats                    false
% 35.86/4.98  
% 35.86/4.98  ------ Abstraction refinement Options
% 35.86/4.98  
% 35.86/4.98  --abstr_ref                             []
% 35.86/4.98  --abstr_ref_prep                        false
% 35.86/4.98  --abstr_ref_until_sat                   false
% 35.86/4.98  --abstr_ref_sig_restrict                funpre
% 35.86/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.86/4.98  --abstr_ref_under                       []
% 35.86/4.98  
% 35.86/4.98  ------ SAT Options
% 35.86/4.98  
% 35.86/4.98  --sat_mode                              false
% 35.86/4.98  --sat_fm_restart_options                ""
% 35.86/4.98  --sat_gr_def                            false
% 35.86/4.98  --sat_epr_types                         true
% 35.86/4.98  --sat_non_cyclic_types                  false
% 35.86/4.98  --sat_finite_models                     false
% 35.86/4.98  --sat_fm_lemmas                         false
% 35.86/4.98  --sat_fm_prep                           false
% 35.86/4.98  --sat_fm_uc_incr                        true
% 35.86/4.98  --sat_out_model                         small
% 35.86/4.98  --sat_out_clauses                       false
% 35.86/4.98  
% 35.86/4.98  ------ QBF Options
% 35.86/4.98  
% 35.86/4.98  --qbf_mode                              false
% 35.86/4.98  --qbf_elim_univ                         false
% 35.86/4.98  --qbf_dom_inst                          none
% 35.86/4.98  --qbf_dom_pre_inst                      false
% 35.86/4.98  --qbf_sk_in                             false
% 35.86/4.98  --qbf_pred_elim                         true
% 35.86/4.98  --qbf_split                             512
% 35.86/4.98  
% 35.86/4.98  ------ BMC1 Options
% 35.86/4.98  
% 35.86/4.98  --bmc1_incremental                      false
% 35.86/4.98  --bmc1_axioms                           reachable_all
% 35.86/4.98  --bmc1_min_bound                        0
% 35.86/4.98  --bmc1_max_bound                        -1
% 35.86/4.98  --bmc1_max_bound_default                -1
% 35.86/4.98  --bmc1_symbol_reachability              true
% 35.86/4.98  --bmc1_property_lemmas                  false
% 35.86/4.98  --bmc1_k_induction                      false
% 35.86/4.98  --bmc1_non_equiv_states                 false
% 35.86/4.98  --bmc1_deadlock                         false
% 35.86/4.98  --bmc1_ucm                              false
% 35.86/4.98  --bmc1_add_unsat_core                   none
% 35.86/4.98  --bmc1_unsat_core_children              false
% 35.86/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.86/4.98  --bmc1_out_stat                         full
% 35.86/4.98  --bmc1_ground_init                      false
% 35.86/4.98  --bmc1_pre_inst_next_state              false
% 35.86/4.98  --bmc1_pre_inst_state                   false
% 35.86/4.98  --bmc1_pre_inst_reach_state             false
% 35.86/4.98  --bmc1_out_unsat_core                   false
% 35.86/4.98  --bmc1_aig_witness_out                  false
% 35.86/4.98  --bmc1_verbose                          false
% 35.86/4.98  --bmc1_dump_clauses_tptp                false
% 35.86/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.86/4.98  --bmc1_dump_file                        -
% 35.86/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.86/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.86/4.98  --bmc1_ucm_extend_mode                  1
% 35.86/4.98  --bmc1_ucm_init_mode                    2
% 35.86/4.98  --bmc1_ucm_cone_mode                    none
% 35.86/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.86/4.98  --bmc1_ucm_relax_model                  4
% 35.86/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.86/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.86/4.98  --bmc1_ucm_layered_model                none
% 35.86/4.98  --bmc1_ucm_max_lemma_size               10
% 35.86/4.98  
% 35.86/4.98  ------ AIG Options
% 35.86/4.98  
% 35.86/4.98  --aig_mode                              false
% 35.86/4.98  
% 35.86/4.98  ------ Instantiation Options
% 35.86/4.98  
% 35.86/4.98  --instantiation_flag                    true
% 35.86/4.98  --inst_sos_flag                         false
% 35.86/4.98  --inst_sos_phase                        true
% 35.86/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.86/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.86/4.98  --inst_lit_sel_side                     num_symb
% 35.86/4.98  --inst_solver_per_active                1400
% 35.86/4.98  --inst_solver_calls_frac                1.
% 35.86/4.98  --inst_passive_queue_type               priority_queues
% 35.86/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.86/4.98  --inst_passive_queues_freq              [25;2]
% 35.86/4.98  --inst_dismatching                      true
% 35.86/4.98  --inst_eager_unprocessed_to_passive     true
% 35.86/4.98  --inst_prop_sim_given                   true
% 35.86/4.98  --inst_prop_sim_new                     false
% 35.86/4.98  --inst_subs_new                         false
% 35.86/4.98  --inst_eq_res_simp                      false
% 35.86/4.98  --inst_subs_given                       false
% 35.86/4.98  --inst_orphan_elimination               true
% 35.86/4.98  --inst_learning_loop_flag               true
% 35.86/4.98  --inst_learning_start                   3000
% 35.86/4.98  --inst_learning_factor                  2
% 35.86/4.98  --inst_start_prop_sim_after_learn       3
% 35.86/4.98  --inst_sel_renew                        solver
% 35.86/4.98  --inst_lit_activity_flag                true
% 35.86/4.98  --inst_restr_to_given                   false
% 35.86/4.98  --inst_activity_threshold               500
% 35.86/4.98  --inst_out_proof                        true
% 35.86/4.98  
% 35.86/4.98  ------ Resolution Options
% 35.86/4.98  
% 35.86/4.98  --resolution_flag                       true
% 35.86/4.98  --res_lit_sel                           adaptive
% 35.86/4.98  --res_lit_sel_side                      none
% 35.86/4.98  --res_ordering                          kbo
% 35.86/4.98  --res_to_prop_solver                    active
% 35.86/4.98  --res_prop_simpl_new                    false
% 35.86/4.98  --res_prop_simpl_given                  true
% 35.86/4.98  --res_passive_queue_type                priority_queues
% 35.86/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.86/4.98  --res_passive_queues_freq               [15;5]
% 35.86/4.98  --res_forward_subs                      full
% 35.86/4.98  --res_backward_subs                     full
% 35.86/4.98  --res_forward_subs_resolution           true
% 35.86/4.98  --res_backward_subs_resolution          true
% 35.86/4.98  --res_orphan_elimination                true
% 35.86/4.98  --res_time_limit                        2.
% 35.86/4.98  --res_out_proof                         true
% 35.86/4.98  
% 35.86/4.98  ------ Superposition Options
% 35.86/4.98  
% 35.86/4.98  --superposition_flag                    true
% 35.86/4.98  --sup_passive_queue_type                priority_queues
% 35.86/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.86/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.86/4.98  --demod_completeness_check              fast
% 35.86/4.98  --demod_use_ground                      true
% 35.86/4.98  --sup_to_prop_solver                    passive
% 35.86/4.98  --sup_prop_simpl_new                    true
% 35.86/4.98  --sup_prop_simpl_given                  true
% 35.86/4.98  --sup_fun_splitting                     false
% 35.86/4.98  --sup_smt_interval                      50000
% 35.86/4.98  
% 35.86/4.98  ------ Superposition Simplification Setup
% 35.86/4.98  
% 35.86/4.98  --sup_indices_passive                   []
% 35.86/4.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.86/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_full_bw                           [BwDemod]
% 35.86/4.98  --sup_immed_triv                        [TrivRules]
% 35.86/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.86/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_immed_bw_main                     []
% 35.86/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.86/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.86/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.86/4.98  
% 35.86/4.98  ------ Combination Options
% 35.86/4.98  
% 35.86/4.98  --comb_res_mult                         3
% 35.86/4.98  --comb_sup_mult                         2
% 35.86/4.98  --comb_inst_mult                        10
% 35.86/4.98  
% 35.86/4.98  ------ Debug Options
% 35.86/4.98  
% 35.86/4.98  --dbg_backtrace                         false
% 35.86/4.98  --dbg_dump_prop_clauses                 false
% 35.86/4.98  --dbg_dump_prop_clauses_file            -
% 35.86/4.98  --dbg_out_stat                          false
% 35.86/4.98  ------ Parsing...
% 35.86/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.86/4.98  ------ Proving...
% 35.86/4.98  ------ Problem Properties 
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  clauses                                 42
% 35.86/4.98  conjectures                             3
% 35.86/4.98  EPR                                     9
% 35.86/4.98  Horn                                    27
% 35.86/4.98  unary                                   9
% 35.86/4.98  binary                                  8
% 35.86/4.98  lits                                    113
% 35.86/4.98  lits eq                                 12
% 35.86/4.98  fd_pure                                 0
% 35.86/4.98  fd_pseudo                               0
% 35.86/4.98  fd_cond                                 3
% 35.86/4.98  fd_pseudo_cond                          5
% 35.86/4.98  AC symbols                              0
% 35.86/4.98  
% 35.86/4.98  ------ Schedule dynamic 5 is on 
% 35.86/4.98  
% 35.86/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  ------ 
% 35.86/4.98  Current options:
% 35.86/4.98  ------ 
% 35.86/4.98  
% 35.86/4.98  ------ Input Options
% 35.86/4.98  
% 35.86/4.98  --out_options                           all
% 35.86/4.98  --tptp_safe_out                         true
% 35.86/4.98  --problem_path                          ""
% 35.86/4.98  --include_path                          ""
% 35.86/4.98  --clausifier                            res/vclausify_rel
% 35.86/4.98  --clausifier_options                    --mode clausify
% 35.86/4.98  --stdin                                 false
% 35.86/4.98  --stats_out                             all
% 35.86/4.98  
% 35.86/4.98  ------ General Options
% 35.86/4.98  
% 35.86/4.98  --fof                                   false
% 35.86/4.98  --time_out_real                         305.
% 35.86/4.98  --time_out_virtual                      -1.
% 35.86/4.98  --symbol_type_check                     false
% 35.86/4.98  --clausify_out                          false
% 35.86/4.98  --sig_cnt_out                           false
% 35.86/4.98  --trig_cnt_out                          false
% 35.86/4.98  --trig_cnt_out_tolerance                1.
% 35.86/4.98  --trig_cnt_out_sk_spl                   false
% 35.86/4.98  --abstr_cl_out                          false
% 35.86/4.98  
% 35.86/4.98  ------ Global Options
% 35.86/4.98  
% 35.86/4.98  --schedule                              default
% 35.86/4.98  --add_important_lit                     false
% 35.86/4.98  --prop_solver_per_cl                    1000
% 35.86/4.98  --min_unsat_core                        false
% 35.86/4.98  --soft_assumptions                      false
% 35.86/4.98  --soft_lemma_size                       3
% 35.86/4.98  --prop_impl_unit_size                   0
% 35.86/4.98  --prop_impl_unit                        []
% 35.86/4.98  --share_sel_clauses                     true
% 35.86/4.98  --reset_solvers                         false
% 35.86/4.98  --bc_imp_inh                            [conj_cone]
% 35.86/4.98  --conj_cone_tolerance                   3.
% 35.86/4.98  --extra_neg_conj                        none
% 35.86/4.98  --large_theory_mode                     true
% 35.86/4.98  --prolific_symb_bound                   200
% 35.86/4.98  --lt_threshold                          2000
% 35.86/4.98  --clause_weak_htbl                      true
% 35.86/4.98  --gc_record_bc_elim                     false
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing Options
% 35.86/4.98  
% 35.86/4.98  --preprocessing_flag                    true
% 35.86/4.98  --time_out_prep_mult                    0.1
% 35.86/4.98  --splitting_mode                        input
% 35.86/4.98  --splitting_grd                         true
% 35.86/4.98  --splitting_cvd                         false
% 35.86/4.98  --splitting_cvd_svl                     false
% 35.86/4.98  --splitting_nvd                         32
% 35.86/4.98  --sub_typing                            true
% 35.86/4.98  --prep_gs_sim                           true
% 35.86/4.98  --prep_unflatten                        true
% 35.86/4.98  --prep_res_sim                          true
% 35.86/4.98  --prep_upred                            true
% 35.86/4.98  --prep_sem_filter                       exhaustive
% 35.86/4.98  --prep_sem_filter_out                   false
% 35.86/4.98  --pred_elim                             true
% 35.86/4.98  --res_sim_input                         true
% 35.86/4.98  --eq_ax_congr_red                       true
% 35.86/4.98  --pure_diseq_elim                       true
% 35.86/4.98  --brand_transform                       false
% 35.86/4.98  --non_eq_to_eq                          false
% 35.86/4.98  --prep_def_merge                        true
% 35.86/4.98  --prep_def_merge_prop_impl              false
% 35.86/4.98  --prep_def_merge_mbd                    true
% 35.86/4.98  --prep_def_merge_tr_red                 false
% 35.86/4.98  --prep_def_merge_tr_cl                  false
% 35.86/4.98  --smt_preprocessing                     true
% 35.86/4.98  --smt_ac_axioms                         fast
% 35.86/4.98  --preprocessed_out                      false
% 35.86/4.98  --preprocessed_stats                    false
% 35.86/4.98  
% 35.86/4.98  ------ Abstraction refinement Options
% 35.86/4.98  
% 35.86/4.98  --abstr_ref                             []
% 35.86/4.98  --abstr_ref_prep                        false
% 35.86/4.98  --abstr_ref_until_sat                   false
% 35.86/4.98  --abstr_ref_sig_restrict                funpre
% 35.86/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.86/4.98  --abstr_ref_under                       []
% 35.86/4.98  
% 35.86/4.98  ------ SAT Options
% 35.86/4.98  
% 35.86/4.98  --sat_mode                              false
% 35.86/4.98  --sat_fm_restart_options                ""
% 35.86/4.98  --sat_gr_def                            false
% 35.86/4.98  --sat_epr_types                         true
% 35.86/4.98  --sat_non_cyclic_types                  false
% 35.86/4.98  --sat_finite_models                     false
% 35.86/4.98  --sat_fm_lemmas                         false
% 35.86/4.98  --sat_fm_prep                           false
% 35.86/4.98  --sat_fm_uc_incr                        true
% 35.86/4.98  --sat_out_model                         small
% 35.86/4.98  --sat_out_clauses                       false
% 35.86/4.98  
% 35.86/4.98  ------ QBF Options
% 35.86/4.98  
% 35.86/4.98  --qbf_mode                              false
% 35.86/4.98  --qbf_elim_univ                         false
% 35.86/4.98  --qbf_dom_inst                          none
% 35.86/4.98  --qbf_dom_pre_inst                      false
% 35.86/4.98  --qbf_sk_in                             false
% 35.86/4.98  --qbf_pred_elim                         true
% 35.86/4.98  --qbf_split                             512
% 35.86/4.98  
% 35.86/4.98  ------ BMC1 Options
% 35.86/4.98  
% 35.86/4.98  --bmc1_incremental                      false
% 35.86/4.98  --bmc1_axioms                           reachable_all
% 35.86/4.98  --bmc1_min_bound                        0
% 35.86/4.98  --bmc1_max_bound                        -1
% 35.86/4.98  --bmc1_max_bound_default                -1
% 35.86/4.98  --bmc1_symbol_reachability              true
% 35.86/4.98  --bmc1_property_lemmas                  false
% 35.86/4.98  --bmc1_k_induction                      false
% 35.86/4.98  --bmc1_non_equiv_states                 false
% 35.86/4.98  --bmc1_deadlock                         false
% 35.86/4.98  --bmc1_ucm                              false
% 35.86/4.98  --bmc1_add_unsat_core                   none
% 35.86/4.98  --bmc1_unsat_core_children              false
% 35.86/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.86/4.98  --bmc1_out_stat                         full
% 35.86/4.98  --bmc1_ground_init                      false
% 35.86/4.98  --bmc1_pre_inst_next_state              false
% 35.86/4.98  --bmc1_pre_inst_state                   false
% 35.86/4.98  --bmc1_pre_inst_reach_state             false
% 35.86/4.98  --bmc1_out_unsat_core                   false
% 35.86/4.98  --bmc1_aig_witness_out                  false
% 35.86/4.98  --bmc1_verbose                          false
% 35.86/4.98  --bmc1_dump_clauses_tptp                false
% 35.86/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.86/4.98  --bmc1_dump_file                        -
% 35.86/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.86/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.86/4.98  --bmc1_ucm_extend_mode                  1
% 35.86/4.98  --bmc1_ucm_init_mode                    2
% 35.86/4.98  --bmc1_ucm_cone_mode                    none
% 35.86/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.86/4.98  --bmc1_ucm_relax_model                  4
% 35.86/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.86/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.86/4.98  --bmc1_ucm_layered_model                none
% 35.86/4.98  --bmc1_ucm_max_lemma_size               10
% 35.86/4.98  
% 35.86/4.98  ------ AIG Options
% 35.86/4.98  
% 35.86/4.98  --aig_mode                              false
% 35.86/4.98  
% 35.86/4.98  ------ Instantiation Options
% 35.86/4.98  
% 35.86/4.98  --instantiation_flag                    true
% 35.86/4.98  --inst_sos_flag                         false
% 35.86/4.98  --inst_sos_phase                        true
% 35.86/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.86/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.86/4.98  --inst_lit_sel_side                     none
% 35.86/4.98  --inst_solver_per_active                1400
% 35.86/4.98  --inst_solver_calls_frac                1.
% 35.86/4.98  --inst_passive_queue_type               priority_queues
% 35.86/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.86/4.98  --inst_passive_queues_freq              [25;2]
% 35.86/4.98  --inst_dismatching                      true
% 35.86/4.98  --inst_eager_unprocessed_to_passive     true
% 35.86/4.98  --inst_prop_sim_given                   true
% 35.86/4.98  --inst_prop_sim_new                     false
% 35.86/4.98  --inst_subs_new                         false
% 35.86/4.98  --inst_eq_res_simp                      false
% 35.86/4.98  --inst_subs_given                       false
% 35.86/4.98  --inst_orphan_elimination               true
% 35.86/4.98  --inst_learning_loop_flag               true
% 35.86/4.98  --inst_learning_start                   3000
% 35.86/4.98  --inst_learning_factor                  2
% 35.86/4.98  --inst_start_prop_sim_after_learn       3
% 35.86/4.98  --inst_sel_renew                        solver
% 35.86/4.98  --inst_lit_activity_flag                true
% 35.86/4.98  --inst_restr_to_given                   false
% 35.86/4.98  --inst_activity_threshold               500
% 35.86/4.98  --inst_out_proof                        true
% 35.86/4.98  
% 35.86/4.98  ------ Resolution Options
% 35.86/4.98  
% 35.86/4.98  --resolution_flag                       false
% 35.86/4.98  --res_lit_sel                           adaptive
% 35.86/4.98  --res_lit_sel_side                      none
% 35.86/4.98  --res_ordering                          kbo
% 35.86/4.98  --res_to_prop_solver                    active
% 35.86/4.98  --res_prop_simpl_new                    false
% 35.86/4.98  --res_prop_simpl_given                  true
% 35.86/4.98  --res_passive_queue_type                priority_queues
% 35.86/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.86/4.98  --res_passive_queues_freq               [15;5]
% 35.86/4.98  --res_forward_subs                      full
% 35.86/4.98  --res_backward_subs                     full
% 35.86/4.98  --res_forward_subs_resolution           true
% 35.86/4.98  --res_backward_subs_resolution          true
% 35.86/4.98  --res_orphan_elimination                true
% 35.86/4.98  --res_time_limit                        2.
% 35.86/4.98  --res_out_proof                         true
% 35.86/4.98  
% 35.86/4.98  ------ Superposition Options
% 35.86/4.98  
% 35.86/4.98  --superposition_flag                    true
% 35.86/4.98  --sup_passive_queue_type                priority_queues
% 35.86/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.86/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.86/4.98  --demod_completeness_check              fast
% 35.86/4.98  --demod_use_ground                      true
% 35.86/4.98  --sup_to_prop_solver                    passive
% 35.86/4.98  --sup_prop_simpl_new                    true
% 35.86/4.98  --sup_prop_simpl_given                  true
% 35.86/4.98  --sup_fun_splitting                     false
% 35.86/4.98  --sup_smt_interval                      50000
% 35.86/4.98  
% 35.86/4.98  ------ Superposition Simplification Setup
% 35.86/4.98  
% 35.86/4.98  --sup_indices_passive                   []
% 35.86/4.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.86/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.86/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_full_bw                           [BwDemod]
% 35.86/4.98  --sup_immed_triv                        [TrivRules]
% 35.86/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.86/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_immed_bw_main                     []
% 35.86/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.86/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.86/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.86/4.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.86/4.98  
% 35.86/4.98  ------ Combination Options
% 35.86/4.98  
% 35.86/4.98  --comb_res_mult                         3
% 35.86/4.98  --comb_sup_mult                         2
% 35.86/4.98  --comb_inst_mult                        10
% 35.86/4.98  
% 35.86/4.98  ------ Debug Options
% 35.86/4.98  
% 35.86/4.98  --dbg_backtrace                         false
% 35.86/4.98  --dbg_dump_prop_clauses                 false
% 35.86/4.98  --dbg_dump_prop_clauses_file            -
% 35.86/4.98  --dbg_out_stat                          false
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  ------ Proving...
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  % SZS status Theorem for theBenchmark.p
% 35.86/4.98  
% 35.86/4.98   Resolution empty clause
% 35.86/4.98  
% 35.86/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.86/4.98  
% 35.86/4.98  fof(f7,axiom,(
% 35.86/4.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f94,plain,(
% 35.86/4.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(cnf_transformation,[],[f7])).
% 35.86/4.98  
% 35.86/4.98  fof(f6,axiom,(
% 35.86/4.98    ! [X0] : k2_subset_1(X0) = X0),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f93,plain,(
% 35.86/4.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 35.86/4.98    inference(cnf_transformation,[],[f6])).
% 35.86/4.98  
% 35.86/4.98  fof(f15,axiom,(
% 35.86/4.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f37,plain,(
% 35.86/4.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(ennf_transformation,[],[f15])).
% 35.86/4.98  
% 35.86/4.98  fof(f38,plain,(
% 35.86/4.98    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(flattening,[],[f37])).
% 35.86/4.98  
% 35.86/4.98  fof(f68,plain,(
% 35.86/4.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(nnf_transformation,[],[f38])).
% 35.86/4.98  
% 35.86/4.98  fof(f69,plain,(
% 35.86/4.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(rectify,[],[f68])).
% 35.86/4.98  
% 35.86/4.98  fof(f71,plain,(
% 35.86/4.98    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK7(X0,X1),X1) & r1_orders_2(X0,X2,sK7(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))))) )),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f70,plain,(
% 35.86/4.98    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK6(X0,X1),X3) & r2_hidden(sK6(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f72,plain,(
% 35.86/4.98    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK7(X0,X1),X1) & r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1)) & r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f69,f71,f70])).
% 35.86/4.98  
% 35.86/4.98  fof(f114,plain,(
% 35.86/4.98    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | r2_hidden(sK6(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f72])).
% 35.86/4.98  
% 35.86/4.98  fof(f17,conjecture,(
% 35.86/4.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f18,negated_conjecture,(
% 35.86/4.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 35.86/4.98    inference(negated_conjecture,[],[f17])).
% 35.86/4.98  
% 35.86/4.98  fof(f19,plain,(
% 35.86/4.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 35.86/4.98    inference(pure_predicate_removal,[],[f18])).
% 35.86/4.98  
% 35.86/4.98  fof(f20,plain,(
% 35.86/4.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 35.86/4.98    inference(pure_predicate_removal,[],[f19])).
% 35.86/4.98  
% 35.86/4.98  fof(f21,plain,(
% 35.86/4.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 35.86/4.98    inference(pure_predicate_removal,[],[f20])).
% 35.86/4.98  
% 35.86/4.98  fof(f40,plain,(
% 35.86/4.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f21])).
% 35.86/4.98  
% 35.86/4.98  fof(f41,plain,(
% 35.86/4.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 35.86/4.98    inference(flattening,[],[f40])).
% 35.86/4.98  
% 35.86/4.98  fof(f74,plain,(
% 35.86/4.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 35.86/4.98    inference(nnf_transformation,[],[f41])).
% 35.86/4.98  
% 35.86/4.98  fof(f75,plain,(
% 35.86/4.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 35.86/4.98    inference(flattening,[],[f74])).
% 35.86/4.98  
% 35.86/4.98  fof(f77,plain,(
% 35.86/4.98    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK9) | ~v1_subset_1(sK9,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK9) | v1_subset_1(sK9,u1_struct_0(X0))) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK9,X0) & ~v1_xboole_0(sK9))) )),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f76,plain,(
% 35.86/4.98    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK8),X1) | ~v1_subset_1(X1,u1_struct_0(sK8))) & (~r2_hidden(k3_yellow_0(sK8),X1) | v1_subset_1(X1,u1_struct_0(sK8))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) & v13_waybel_0(X1,sK8) & ~v1_xboole_0(X1)) & l1_orders_2(sK8) & v1_yellow_0(sK8) & v5_orders_2(sK8) & ~v2_struct_0(sK8))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f78,plain,(
% 35.86/4.98    ((r2_hidden(k3_yellow_0(sK8),sK9) | ~v1_subset_1(sK9,u1_struct_0(sK8))) & (~r2_hidden(k3_yellow_0(sK8),sK9) | v1_subset_1(sK9,u1_struct_0(sK8))) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) & v13_waybel_0(sK9,sK8) & ~v1_xboole_0(sK9)) & l1_orders_2(sK8) & v1_yellow_0(sK8) & v5_orders_2(sK8) & ~v2_struct_0(sK8)),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f75,f77,f76])).
% 35.86/4.98  
% 35.86/4.98  fof(f122,plain,(
% 35.86/4.98    l1_orders_2(sK8)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f112,plain,(
% 35.86/4.98    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f72])).
% 35.86/4.98  
% 35.86/4.98  fof(f10,axiom,(
% 35.86/4.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f29,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(ennf_transformation,[],[f10])).
% 35.86/4.98  
% 35.86/4.98  fof(f30,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(flattening,[],[f29])).
% 35.86/4.98  
% 35.86/4.98  fof(f59,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(nnf_transformation,[],[f30])).
% 35.86/4.98  
% 35.86/4.98  fof(f60,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(rectify,[],[f59])).
% 35.86/4.98  
% 35.86/4.98  fof(f61,plain,(
% 35.86/4.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f62,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 35.86/4.98  
% 35.86/4.98  fof(f99,plain,(
% 35.86/4.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f62])).
% 35.86/4.98  
% 35.86/4.98  fof(f125,plain,(
% 35.86/4.98    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f16,axiom,(
% 35.86/4.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f39,plain,(
% 35.86/4.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f16])).
% 35.86/4.98  
% 35.86/4.98  fof(f73,plain,(
% 35.86/4.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(nnf_transformation,[],[f39])).
% 35.86/4.98  
% 35.86/4.98  fof(f117,plain,(
% 35.86/4.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(cnf_transformation,[],[f73])).
% 35.86/4.98  
% 35.86/4.98  fof(f132,plain,(
% 35.86/4.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 35.86/4.98    inference(equality_resolution,[],[f117])).
% 35.86/4.98  
% 35.86/4.98  fof(f126,plain,(
% 35.86/4.98    ~r2_hidden(k3_yellow_0(sK8),sK9) | v1_subset_1(sK9,u1_struct_0(sK8))),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f11,axiom,(
% 35.86/4.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f31,plain,(
% 35.86/4.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(ennf_transformation,[],[f11])).
% 35.86/4.98  
% 35.86/4.98  fof(f103,plain,(
% 35.86/4.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f31])).
% 35.86/4.98  
% 35.86/4.98  fof(f13,axiom,(
% 35.86/4.98    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f34,plain,(
% 35.86/4.98    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(ennf_transformation,[],[f13])).
% 35.86/4.98  
% 35.86/4.98  fof(f109,plain,(
% 35.86/4.98    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f34])).
% 35.86/4.98  
% 35.86/4.98  fof(f2,axiom,(
% 35.86/4.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f23,plain,(
% 35.86/4.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f2])).
% 35.86/4.98  
% 35.86/4.98  fof(f46,plain,(
% 35.86/4.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 35.86/4.98    inference(nnf_transformation,[],[f23])).
% 35.86/4.98  
% 35.86/4.98  fof(f47,plain,(
% 35.86/4.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.86/4.98    inference(rectify,[],[f46])).
% 35.86/4.98  
% 35.86/4.98  fof(f48,plain,(
% 35.86/4.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f49,plain,(
% 35.86/4.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 35.86/4.98  
% 35.86/4.98  fof(f82,plain,(
% 35.86/4.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f49])).
% 35.86/4.98  
% 35.86/4.98  fof(f5,axiom,(
% 35.86/4.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f24,plain,(
% 35.86/4.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f5])).
% 35.86/4.98  
% 35.86/4.98  fof(f54,plain,(
% 35.86/4.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 35.86/4.98    inference(nnf_transformation,[],[f24])).
% 35.86/4.98  
% 35.86/4.98  fof(f90,plain,(
% 35.86/4.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f54])).
% 35.86/4.98  
% 35.86/4.98  fof(f1,axiom,(
% 35.86/4.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f42,plain,(
% 35.86/4.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 35.86/4.98    inference(nnf_transformation,[],[f1])).
% 35.86/4.98  
% 35.86/4.98  fof(f43,plain,(
% 35.86/4.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 35.86/4.98    inference(rectify,[],[f42])).
% 35.86/4.98  
% 35.86/4.98  fof(f44,plain,(
% 35.86/4.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f45,plain,(
% 35.86/4.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 35.86/4.98  
% 35.86/4.98  fof(f79,plain,(
% 35.86/4.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f45])).
% 35.86/4.98  
% 35.86/4.98  fof(f111,plain,(
% 35.86/4.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f72])).
% 35.86/4.98  
% 35.86/4.98  fof(f9,axiom,(
% 35.86/4.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f27,plain,(
% 35.86/4.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 35.86/4.98    inference(ennf_transformation,[],[f9])).
% 35.86/4.98  
% 35.86/4.98  fof(f28,plain,(
% 35.86/4.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 35.86/4.98    inference(flattening,[],[f27])).
% 35.86/4.98  
% 35.86/4.98  fof(f98,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f28])).
% 35.86/4.98  
% 35.86/4.98  fof(f124,plain,(
% 35.86/4.98    v13_waybel_0(sK9,sK8)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f123,plain,(
% 35.86/4.98    ~v1_xboole_0(sK9)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f3,axiom,(
% 35.86/4.98    v1_xboole_0(k1_xboole_0)),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f84,plain,(
% 35.86/4.98    v1_xboole_0(k1_xboole_0)),
% 35.86/4.98    inference(cnf_transformation,[],[f3])).
% 35.86/4.98  
% 35.86/4.98  fof(f12,axiom,(
% 35.86/4.98    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f32,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(ennf_transformation,[],[f12])).
% 35.86/4.98  
% 35.86/4.98  fof(f33,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(flattening,[],[f32])).
% 35.86/4.98  
% 35.86/4.98  fof(f63,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(nnf_transformation,[],[f33])).
% 35.86/4.98  
% 35.86/4.98  fof(f64,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(flattening,[],[f63])).
% 35.86/4.98  
% 35.86/4.98  fof(f65,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(rectify,[],[f64])).
% 35.86/4.98  
% 35.86/4.98  fof(f66,plain,(
% 35.86/4.98    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f67,plain,(
% 35.86/4.98    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) & r2_lattice3(X0,X1,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).
% 35.86/4.98  
% 35.86/4.98  fof(f105,plain,(
% 35.86/4.98    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f67])).
% 35.86/4.98  
% 35.86/4.98  fof(f130,plain,(
% 35.86/4.98    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(equality_resolution,[],[f105])).
% 35.86/4.98  
% 35.86/4.98  fof(f14,axiom,(
% 35.86/4.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f22,plain,(
% 35.86/4.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 35.86/4.98    inference(pure_predicate_removal,[],[f14])).
% 35.86/4.98  
% 35.86/4.98  fof(f35,plain,(
% 35.86/4.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f22])).
% 35.86/4.98  
% 35.86/4.98  fof(f36,plain,(
% 35.86/4.98    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 35.86/4.98    inference(flattening,[],[f35])).
% 35.86/4.98  
% 35.86/4.98  fof(f110,plain,(
% 35.86/4.98    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f36])).
% 35.86/4.98  
% 35.86/4.98  fof(f121,plain,(
% 35.86/4.98    v1_yellow_0(sK8)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f119,plain,(
% 35.86/4.98    ~v2_struct_0(sK8)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f120,plain,(
% 35.86/4.98    v5_orders_2(sK8)),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f104,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f67])).
% 35.86/4.98  
% 35.86/4.98  fof(f131,plain,(
% 35.86/4.98    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(equality_resolution,[],[f104])).
% 35.86/4.98  
% 35.86/4.98  fof(f106,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f67])).
% 35.86/4.98  
% 35.86/4.98  fof(f107,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f67])).
% 35.86/4.98  
% 35.86/4.98  fof(f108,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f67])).
% 35.86/4.98  
% 35.86/4.98  fof(f118,plain,(
% 35.86/4.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(cnf_transformation,[],[f73])).
% 35.86/4.98  
% 35.86/4.98  fof(f127,plain,(
% 35.86/4.98    r2_hidden(k3_yellow_0(sK8),sK9) | ~v1_subset_1(sK9,u1_struct_0(sK8))),
% 35.86/4.98    inference(cnf_transformation,[],[f78])).
% 35.86/4.98  
% 35.86/4.98  fof(f89,plain,(
% 35.86/4.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f54])).
% 35.86/4.98  
% 35.86/4.98  fof(f101,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f62])).
% 35.86/4.98  
% 35.86/4.98  fof(f8,axiom,(
% 35.86/4.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f25,plain,(
% 35.86/4.98    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(ennf_transformation,[],[f8])).
% 35.86/4.98  
% 35.86/4.98  fof(f26,plain,(
% 35.86/4.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(flattening,[],[f25])).
% 35.86/4.98  
% 35.86/4.98  fof(f55,plain,(
% 35.86/4.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(nnf_transformation,[],[f26])).
% 35.86/4.98  
% 35.86/4.98  fof(f56,plain,(
% 35.86/4.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(flattening,[],[f55])).
% 35.86/4.98  
% 35.86/4.98  fof(f57,plain,(
% 35.86/4.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f58,plain,(
% 35.86/4.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1)) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 35.86/4.98  
% 35.86/4.98  fof(f95,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK3(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(cnf_transformation,[],[f58])).
% 35.86/4.98  
% 35.86/4.98  fof(f91,plain,(
% 35.86/4.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f54])).
% 35.86/4.98  
% 35.86/4.98  fof(f4,axiom,(
% 35.86/4.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 35.86/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.86/4.98  
% 35.86/4.98  fof(f50,plain,(
% 35.86/4.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.86/4.98    inference(nnf_transformation,[],[f4])).
% 35.86/4.98  
% 35.86/4.98  fof(f51,plain,(
% 35.86/4.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.86/4.98    inference(rectify,[],[f50])).
% 35.86/4.98  
% 35.86/4.98  fof(f52,plain,(
% 35.86/4.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 35.86/4.98    introduced(choice_axiom,[])).
% 35.86/4.98  
% 35.86/4.98  fof(f53,plain,(
% 35.86/4.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.86/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 35.86/4.98  
% 35.86/4.98  fof(f85,plain,(
% 35.86/4.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 35.86/4.98    inference(cnf_transformation,[],[f53])).
% 35.86/4.98  
% 35.86/4.98  fof(f129,plain,(
% 35.86/4.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(equality_resolution,[],[f85])).
% 35.86/4.98  
% 35.86/4.98  fof(f81,plain,(
% 35.86/4.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 35.86/4.98    inference(cnf_transformation,[],[f49])).
% 35.86/4.98  
% 35.86/4.98  fof(f97,plain,(
% 35.86/4.98    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.86/4.98    inference(cnf_transformation,[],[f58])).
% 35.86/4.98  
% 35.86/4.98  cnf(c_15,plain,
% 35.86/4.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 35.86/4.98      inference(cnf_transformation,[],[f94]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3437,plain,
% 35.86/4.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_14,plain,
% 35.86/4.98      ( k2_subset_1(X0) = X0 ),
% 35.86/4.98      inference(cnf_transformation,[],[f93]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3463,plain,
% 35.86/4.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 35.86/4.98      inference(light_normalisation,[status(thm)],[c_3437,c_14]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_34,plain,
% 35.86/4.98      ( v13_waybel_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.86/4.98      | r2_hidden(sK6(X1,X0),X0)
% 35.86/4.98      | ~ l1_orders_2(X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f114]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_45,negated_conjecture,
% 35.86/4.98      ( l1_orders_2(sK8) ),
% 35.86/4.98      inference(cnf_transformation,[],[f122]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1148,plain,
% 35.86/4.98      ( v13_waybel_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.86/4.98      | r2_hidden(sK6(X1,X0),X0)
% 35.86/4.98      | sK8 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_34,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1149,plain,
% 35.86/4.98      ( v13_waybel_0(X0,sK8)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | r2_hidden(sK6(sK8,X0),X0) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1148]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3412,plain,
% 35.86/4.98      ( v13_waybel_0(X0,sK8) = iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(sK6(sK8,X0),X0) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3983,plain,
% 35.86/4.98      ( v13_waybel_0(u1_struct_0(sK8),sK8) = iProver_top
% 35.86/4.98      | r2_hidden(sK6(sK8,u1_struct_0(sK8)),u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3463,c_3412]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_36,plain,
% 35.86/4.98      ( v13_waybel_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.86/4.98      | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
% 35.86/4.98      | ~ l1_orders_2(X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f112]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1118,plain,
% 35.86/4.98      ( v13_waybel_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.86/4.98      | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
% 35.86/4.98      | sK8 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_36,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1119,plain,
% 35.86/4.98      ( v13_waybel_0(X0,sK8)
% 35.86/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1118]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3414,plain,
% 35.86/4.98      ( v13_waybel_0(X0,sK8) = iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | m1_subset_1(sK6(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_23,plain,
% 35.86/4.98      ( r1_orders_2(X0,X1,X2)
% 35.86/4.98      | ~ r2_lattice3(X0,X3,X2)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ r2_hidden(X1,X3)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f99]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1052,plain,
% 35.86/4.98      ( r1_orders_2(X0,X1,X2)
% 35.86/4.98      | ~ r2_lattice3(X0,X3,X2)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ r2_hidden(X1,X3)
% 35.86/4.98      | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_23,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1053,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ r2_lattice3(sK8,X2,X1)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ r2_hidden(X0,X2) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1052]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3418,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,X2,X1) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,X2) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4566,plain,
% 35.86/4.98      ( r1_orders_2(sK8,sK6(sK8,X0),X1) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,X2,X1) != iProver_top
% 35.86/4.98      | v13_waybel_0(X0,sK8) = iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(sK6(sK8,X0),X2) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3414,c_3418]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_11715,plain,
% 35.86/4.98      ( r1_orders_2(sK8,sK6(sK8,u1_struct_0(sK8)),X0) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,u1_struct_0(sK8),X0) != iProver_top
% 35.86/4.98      | v13_waybel_0(u1_struct_0(sK8),sK8) = iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3983,c_4566]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_42,negated_conjecture,
% 35.86/4.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 35.86/4.98      inference(cnf_transformation,[],[f125]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_55,plain,
% 35.86/4.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_39,plain,
% 35.86/4.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 35.86/4.98      inference(cnf_transformation,[],[f132]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_41,negated_conjecture,
% 35.86/4.98      ( v1_subset_1(sK9,u1_struct_0(sK8)) | ~ r2_hidden(k3_yellow_0(sK8),sK9) ),
% 35.86/4.98      inference(cnf_transformation,[],[f126]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_394,plain,
% 35.86/4.98      ( v1_subset_1(sK9,u1_struct_0(sK8)) | ~ r2_hidden(k3_yellow_0(sK8),sK9) ),
% 35.86/4.98      inference(prop_impl,[status(thm)],[c_41]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_686,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 35.86/4.98      | ~ r2_hidden(k3_yellow_0(sK8),sK9)
% 35.86/4.98      | u1_struct_0(sK8) != X0
% 35.86/4.98      | sK9 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_39,c_394]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_687,plain,
% 35.86/4.98      ( ~ m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(k3_yellow_0(sK8),sK9)
% 35.86/4.98      | sK9 != u1_struct_0(sK8) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_686]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3427,plain,
% 35.86/4.98      ( sK9 != u1_struct_0(sK8)
% 35.86/4.98      | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3578,plain,
% 35.86/4.98      ( u1_struct_0(sK8) != sK9
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
% 35.86/4.98      inference(forward_subsumption_resolution,[status(thm)],[c_3427,c_3463]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_24,plain,
% 35.86/4.98      ( ~ l1_orders_2(X0) | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f103]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1047,plain,
% 35.86/4.98      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_24,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1048,plain,
% 35.86/4.98      ( k1_yellow_0(sK8,k1_xboole_0) = k3_yellow_0(sK8) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1047]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_30,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f109]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1038,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_30,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1039,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8)) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1038]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3419,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3858,plain,
% 35.86/4.98      ( m1_subset_1(k3_yellow_0(sK8),u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_1048,c_3419]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3,plain,
% 35.86/4.98      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f82]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3447,plain,
% 35.86/4.98      ( r1_tarski(X0,X1) = iProver_top
% 35.86/4.98      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_12,plain,
% 35.86/4.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f90]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1,plain,
% 35.86/4.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f79]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_312,plain,
% 35.86/4.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_12,c_1]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_313,plain,
% 35.86/4.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_312]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3429,plain,
% 35.86/4.98      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_7695,plain,
% 35.86/4.98      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 35.86/4.98      | r1_tarski(X0,X1) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3447,c_3429]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_11924,plain,
% 35.86/4.98      ( r1_orders_2(sK8,sK1(u1_struct_0(sK8),X0),X1) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,X2,X1) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r1_tarski(u1_struct_0(sK8),X0) = iProver_top
% 35.86/4.98      | r2_hidden(sK1(u1_struct_0(sK8),X0),X2) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_7695,c_3418]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_14683,plain,
% 35.86/4.98      ( r1_orders_2(sK8,sK1(u1_struct_0(sK8),X0),X1) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,u1_struct_0(sK8),X1) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r1_tarski(u1_struct_0(sK8),X0) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3447,c_11924]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3432,plain,
% 35.86/4.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_37,plain,
% 35.86/4.98      ( ~ r1_orders_2(X0,X1,X2)
% 35.86/4.98      | ~ v13_waybel_0(X3,X0)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 35.86/4.98      | ~ r2_hidden(X1,X3)
% 35.86/4.98      | r2_hidden(X2,X3)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f111]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_998,plain,
% 35.86/4.98      ( ~ r1_orders_2(X0,X1,X2)
% 35.86/4.98      | ~ v13_waybel_0(X3,X0)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 35.86/4.98      | ~ r2_hidden(X1,X3)
% 35.86/4.98      | r2_hidden(X2,X3)
% 35.86/4.98      | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_37,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_999,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ v13_waybel_0(X2,sK8)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(X0,X2)
% 35.86/4.98      | r2_hidden(X1,X2) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_998]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_19,plain,
% 35.86/4.98      ( m1_subset_1(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.86/4.98      | ~ r2_hidden(X0,X2) ),
% 35.86/4.98      inference(cnf_transformation,[],[f98]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1015,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ v13_waybel_0(X2,sK8)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(X0,X2)
% 35.86/4.98      | r2_hidden(X1,X2) ),
% 35.86/4.98      inference(forward_subsumption_resolution,[status(thm)],[c_999,c_19]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3421,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1) != iProver_top
% 35.86/4.98      | v13_waybel_0(X2,sK8) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(X0,X2) != iProver_top
% 35.86/4.98      | r2_hidden(X1,X2) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5389,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1) != iProver_top
% 35.86/4.98      | v13_waybel_0(sK9,sK8) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) != iProver_top
% 35.86/4.98      | r2_hidden(X1,sK9) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3432,c_3421]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_43,negated_conjecture,
% 35.86/4.98      ( v13_waybel_0(sK9,sK8) ),
% 35.86/4.98      inference(cnf_transformation,[],[f124]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1226,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(X0,X2)
% 35.86/4.98      | r2_hidden(X1,X2)
% 35.86/4.98      | sK9 != X2
% 35.86/4.98      | sK8 != sK8 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_43,c_1015]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1227,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(X0,sK9)
% 35.86/4.98      | r2_hidden(X1,sK9) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1226]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1228,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) != iProver_top
% 35.86/4.98      | r2_hidden(X1,sK9) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5990,plain,
% 35.86/4.98      ( r1_orders_2(sK8,X0,X1) != iProver_top
% 35.86/4.98      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) != iProver_top
% 35.86/4.98      | r2_hidden(X1,sK9) = iProver_top ),
% 35.86/4.98      inference(global_propositional_subsumption,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_5389,c_55,c_1228]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_142418,plain,
% 35.86/4.98      ( r2_lattice3(sK8,u1_struct_0(sK8),X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r1_tarski(u1_struct_0(sK8),X1) = iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) = iProver_top
% 35.86/4.98      | r2_hidden(sK1(u1_struct_0(sK8),X1),sK9) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_14683,c_5990]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_52,plain,
% 35.86/4.98      ( l1_orders_2(sK8) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_44,negated_conjecture,
% 35.86/4.98      ( ~ v1_xboole_0(sK9) ),
% 35.86/4.98      inference(cnf_transformation,[],[f123]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_53,plain,
% 35.86/4.98      ( v1_xboole_0(sK9) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_54,plain,
% 35.86/4.98      ( v13_waybel_0(sK9,sK8) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5,plain,
% 35.86/4.98      ( v1_xboole_0(k1_xboole_0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f84]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_154,plain,
% 35.86/4.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_28,plain,
% 35.86/4.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 35.86/4.98      | ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f130]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_291,plain,
% 35.86/4.98      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_28,c_30]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_292,plain,
% 35.86/4.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 35.86/4.98      | ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_291]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_31,plain,
% 35.86/4.98      ( r1_yellow_0(X0,k1_xboole_0)
% 35.86/4.98      | v2_struct_0(X0)
% 35.86/4.98      | ~ v5_orders_2(X0)
% 35.86/4.98      | ~ v1_yellow_0(X0)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f110]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_46,negated_conjecture,
% 35.86/4.98      ( v1_yellow_0(sK8) ),
% 35.86/4.98      inference(cnf_transformation,[],[f121]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_656,plain,
% 35.86/4.98      ( r1_yellow_0(X0,k1_xboole_0)
% 35.86/4.98      | v2_struct_0(X0)
% 35.86/4.98      | ~ v5_orders_2(X0)
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_31,c_46]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_657,plain,
% 35.86/4.98      ( r1_yellow_0(sK8,k1_xboole_0)
% 35.86/4.98      | v2_struct_0(sK8)
% 35.86/4.98      | ~ v5_orders_2(sK8)
% 35.86/4.98      | ~ l1_orders_2(sK8) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_656]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_48,negated_conjecture,
% 35.86/4.98      ( ~ v2_struct_0(sK8) ),
% 35.86/4.98      inference(cnf_transformation,[],[f119]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_47,negated_conjecture,
% 35.86/4.98      ( v5_orders_2(sK8) ),
% 35.86/4.98      inference(cnf_transformation,[],[f120]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_81,plain,
% 35.86/4.98      ( r1_yellow_0(sK8,k1_xboole_0)
% 35.86/4.98      | v2_struct_0(sK8)
% 35.86/4.98      | ~ v5_orders_2(sK8)
% 35.86/4.98      | ~ v1_yellow_0(sK8)
% 35.86/4.98      | ~ l1_orders_2(sK8) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_31]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_659,plain,
% 35.86/4.98      ( r1_yellow_0(sK8,k1_xboole_0) ),
% 35.86/4.98      inference(global_propositional_subsumption,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_657,c_48,c_47,c_46,c_45,c_81]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_730,plain,
% 35.86/4.98      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 35.86/4.98      | ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | sK8 != X0
% 35.86/4.98      | k1_xboole_0 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_292,c_659]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_731,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ l1_orders_2(sK8) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_730]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_732,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | l1_orders_2(sK8) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_29,plain,
% 35.86/4.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f131]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_284,plain,
% 35.86/4.98      ( ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_29,c_30]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_285,plain,
% 35.86/4.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_284]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_751,plain,
% 35.86/4.98      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | sK8 != X0
% 35.86/4.98      | k1_xboole_0 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_285,c_659]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_752,plain,
% 35.86/4.98      ( r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
% 35.86/4.98      | ~ l1_orders_2(sK8) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_751]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_27,plain,
% 35.86/4.98      ( ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X1) = X2 ),
% 35.86/4.98      inference(cnf_transformation,[],[f106]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_762,plain,
% 35.86/4.98      ( ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X1) = X2
% 35.86/4.98      | sK8 != X0
% 35.86/4.98      | k1_xboole_0 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_27,c_659]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_763,plain,
% 35.86/4.98      ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
% 35.86/4.98      | ~ l1_orders_2(sK8)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_762]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_767,plain,
% 35.86/4.98      ( m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_763,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_768,plain,
% 35.86/4.98      ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | m1_subset_1(sK5(sK8,k1_xboole_0,X0),u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_767]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3812,plain,
% 35.86/4.98      ( ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
% 35.86/4.98      | m1_subset_1(sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)),u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_768]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_26,plain,
% 35.86/4.98      ( ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
% 35.86/4.98      | ~ r1_yellow_0(X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X1) = X2 ),
% 35.86/4.98      inference(cnf_transformation,[],[f107]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_786,plain,
% 35.86/4.98      ( ~ r2_lattice3(X0,X1,X2)
% 35.86/4.98      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X1) = X2
% 35.86/4.98      | sK8 != X0
% 35.86/4.98      | k1_xboole_0 != X1 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_26,c_659]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_787,plain,
% 35.86/4.98      ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ l1_orders_2(sK8)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_786]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_791,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_787,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_792,plain,
% 35.86/4.98      ( ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_791]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3815,plain,
% 35.86/4.98      ( r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_792]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_25,plain,
% 35.86/4.98      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 35.86/4.98      | ~ r2_lattice3(X0,X2,X1)
% 35.86/4.98      | ~ r1_yellow_0(X0,X2)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X2) = X1 ),
% 35.86/4.98      inference(cnf_transformation,[],[f108]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_706,plain,
% 35.86/4.98      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 35.86/4.98      | ~ r2_lattice3(X0,X2,X1)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 35.86/4.98      | ~ l1_orders_2(X0)
% 35.86/4.98      | k1_yellow_0(X0,X2) = X1
% 35.86/4.98      | sK8 != X0
% 35.86/4.98      | k1_xboole_0 != X2 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_25,c_659]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_707,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ l1_orders_2(sK8)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_706]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_711,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_707,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_712,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,sK5(sK8,k1_xboole_0,X0))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = X0 ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_711]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3818,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0))
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) = k1_yellow_0(sK8,k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_712]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_2503,plain,( X0 = X0 ),theory(equality) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4095,plain,
% 35.86/4.98      ( sK9 = sK9 ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_2503]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4732,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_1039]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4733,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_4732]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_2504,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3972,plain,
% 35.86/4.98      ( u1_struct_0(sK8) != X0 | sK9 != X0 | sK9 = u1_struct_0(sK8) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_2504]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4804,plain,
% 35.86/4.98      ( u1_struct_0(sK8) != sK9 | sK9 = u1_struct_0(sK8) | sK9 != sK9 ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_3972]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_38,plain,
% 35.86/4.98      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 35.86/4.98      inference(cnf_transformation,[],[f118]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_40,negated_conjecture,
% 35.86/4.98      ( ~ v1_subset_1(sK9,u1_struct_0(sK8)) | r2_hidden(k3_yellow_0(sK8),sK9) ),
% 35.86/4.98      inference(cnf_transformation,[],[f127]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_396,plain,
% 35.86/4.98      ( ~ v1_subset_1(sK9,u1_struct_0(sK8)) | r2_hidden(k3_yellow_0(sK8),sK9) ),
% 35.86/4.98      inference(prop_impl,[status(thm)],[c_40]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_672,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9)
% 35.86/4.98      | X1 = X0
% 35.86/4.98      | u1_struct_0(sK8) != X1
% 35.86/4.98      | sK9 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_38,c_396]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_673,plain,
% 35.86/4.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9)
% 35.86/4.98      | u1_struct_0(sK8) = sK9 ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_672]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_675,plain,
% 35.86/4.98      ( r2_hidden(k3_yellow_0(sK8),sK9) | u1_struct_0(sK8) = sK9 ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_673,c_42]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3428,plain,
% 35.86/4.98      ( u1_struct_0(sK8) = sK9
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_735,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) ),
% 35.86/4.98      inference(global_propositional_subsumption,[status(thm)],[c_731,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_736,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_735]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3425,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3587,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k3_yellow_0(sK8),X0) = iProver_top
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 35.86/4.98      inference(light_normalisation,[status(thm)],[c_3425,c_1048]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5999,plain,
% 35.86/4.98      ( r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) = iProver_top
% 35.86/4.98      | r2_hidden(k3_yellow_0(sK8),sK9) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3587,c_5990]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_6448,plain,
% 35.86/4.98      ( u1_struct_0(sK8) = sK9
% 35.86/4.98      | r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3428,c_5999]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_9165,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
% 35.86/4.98      | ~ r2_lattice3(sK8,k1_xboole_0,sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)))
% 35.86/4.98      | ~ m1_subset_1(sK5(sK8,k1_xboole_0,k1_yellow_0(sK8,k1_xboole_0)),u1_struct_0(sK8)) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_736]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3821,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,X0,X1)
% 35.86/4.98      | ~ v13_waybel_0(sK9,sK8)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ r2_hidden(X0,sK9)
% 35.86/4.98      | r2_hidden(X1,sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_1015]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_65030,plain,
% 35.86/4.98      ( ~ r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0)
% 35.86/4.98      | ~ v13_waybel_0(sK9,sK8)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | r2_hidden(X0,sK9)
% 35.86/4.98      | ~ r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_3821]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_65031,plain,
% 35.86/4.98      ( r1_orders_2(sK8,k1_yellow_0(sK8,k1_xboole_0),X0) != iProver_top
% 35.86/4.98      | v13_waybel_0(sK9,sK8) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) = iProver_top
% 35.86/4.98      | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_65030]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_2509,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.86/4.98      theory(equality) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4051,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,sK9) | X2 != X0 | sK9 != X1 ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_2509]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5219,plain,
% 35.86/4.98      ( m1_subset_1(X0,sK9)
% 35.86/4.98      | ~ m1_subset_1(k1_yellow_0(sK8,X1),u1_struct_0(sK8))
% 35.86/4.98      | X0 != k1_yellow_0(sK8,X1)
% 35.86/4.98      | sK9 != u1_struct_0(sK8) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_4051]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_10410,plain,
% 35.86/4.98      ( ~ m1_subset_1(k1_yellow_0(sK8,X0),u1_struct_0(sK8))
% 35.86/4.98      | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,X0)
% 35.86/4.98      | sK9 != u1_struct_0(sK8) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_5219]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_89531,plain,
% 35.86/4.98      ( ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8))
% 35.86/4.98      | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
% 35.86/4.98      | k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,k1_xboole_0)
% 35.86/4.98      | sK9 != u1_struct_0(sK8) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_10410]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_89532,plain,
% 35.86/4.98      ( k1_yellow_0(sK8,k1_xboole_0) != k1_yellow_0(sK8,k1_xboole_0)
% 35.86/4.98      | sK9 != u1_struct_0(sK8)
% 35.86/4.98      | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_89531]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_13,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f89]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3892,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,sK9) | r2_hidden(X0,sK9) | v1_xboole_0(sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_13]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_108550,plain,
% 35.86/4.98      ( ~ m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9)
% 35.86/4.98      | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9)
% 35.86/4.98      | v1_xboole_0(sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_3892]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_108551,plain,
% 35.86/4.98      ( m1_subset_1(k1_yellow_0(sK8,k1_xboole_0),sK9) != iProver_top
% 35.86/4.98      | r2_hidden(k1_yellow_0(sK8,k1_xboole_0),sK9) = iProver_top
% 35.86/4.98      | v1_xboole_0(sK9) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_108550]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_133020,plain,
% 35.86/4.98      ( ~ r2_hidden(X0,k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_1]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_134909,plain,
% 35.86/4.98      ( ~ r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0)
% 35.86/4.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_133020]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_134911,plain,
% 35.86/4.98      ( r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) != iProver_top
% 35.86/4.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_134909]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_21,plain,
% 35.86/4.98      ( r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | r2_hidden(sK4(X0,X1,X2),X1)
% 35.86/4.98      | ~ l1_orders_2(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f101]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1088,plain,
% 35.86/4.98      ( r2_lattice3(X0,X1,X2)
% 35.86/4.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 35.86/4.98      | r2_hidden(sK4(X0,X1,X2),X1)
% 35.86/4.98      | sK8 != X0 ),
% 35.86/4.98      inference(resolution_lifted,[status(thm)],[c_21,c_45]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_1089,plain,
% 35.86/4.98      ( r2_lattice3(sK8,X0,X1)
% 35.86/4.98      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 35.86/4.98      | r2_hidden(sK4(sK8,X0,X1),X0) ),
% 35.86/4.98      inference(unflattening,[status(thm)],[c_1088]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_134910,plain,
% 35.86/4.98      ( r2_lattice3(sK8,k1_xboole_0,X0)
% 35.86/4.98      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 35.86/4.98      | r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_1089]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_134915,plain,
% 35.86/4.98      ( r2_lattice3(sK8,k1_xboole_0,X0) = iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(sK4(sK8,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_134910]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_145104,plain,
% 35.86/4.98      ( r2_hidden(X0,sK9) = iProver_top
% 35.86/4.98      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top ),
% 35.86/4.98      inference(global_propositional_subsumption,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_142418,c_45,c_52,c_53,c_54,c_55,c_154,c_732,c_752,c_3812,
% 35.86/4.98                 c_3815,c_3818,c_4095,c_4732,c_4733,c_4804,c_6448,c_9165,
% 35.86/4.98                 c_65031,c_89532,c_108551,c_134911,c_134915]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_145105,plain,
% 35.86/4.98      ( m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) = iProver_top ),
% 35.86/4.98      inference(renaming,[status(thm)],[c_145104]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_145120,plain,
% 35.86/4.98      ( r2_hidden(k3_yellow_0(sK8),sK9) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3858,c_145105]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_18,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.86/4.98      | m1_subset_1(sK3(X1,X2,X0),X1)
% 35.86/4.98      | X2 = X0 ),
% 35.86/4.98      inference(cnf_transformation,[],[f95]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3434,plain,
% 35.86/4.98      ( X0 = X1
% 35.86/4.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 35.86/4.98      | m1_subset_1(sK3(X2,X0,X1),X2) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_145113,plain,
% 35.86/4.98      ( X0 = X1
% 35.86/4.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(u1_struct_0(sK8),X1,X0),sK9) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3434,c_145105]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3438,plain,
% 35.86/4.98      ( m1_subset_1(X0,X1) != iProver_top
% 35.86/4.98      | r2_hidden(X0,X1) = iProver_top
% 35.86/4.98      | v1_xboole_0(X1) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5529,plain,
% 35.86/4.98      ( r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
% 35.86/4.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_3432,c_3438]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_11,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 35.86/4.98      inference(cnf_transformation,[],[f91]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3871,plain,
% 35.86/4.98      ( ~ m1_subset_1(sK9,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_11]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4015,plain,
% 35.86/4.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | v1_xboole_0(sK9) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_3871]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4016,plain,
% 35.86/4.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | v1_xboole_0(sK9) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_4015]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4126,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_13]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5044,plain,
% 35.86/4.98      ( ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.86/4.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) ),
% 35.86/4.98      inference(instantiation,[status(thm)],[c_4126]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_5045,plain,
% 35.86/4.98      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
% 35.86/4.98      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_5044]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_6026,plain,
% 35.86/4.98      ( r2_hidden(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.86/4.98      inference(global_propositional_subsumption,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_5529,c_53,c_55,c_4016,c_5045]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_9,plain,
% 35.86/4.98      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 35.86/4.98      inference(cnf_transformation,[],[f129]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3441,plain,
% 35.86/4.98      ( r1_tarski(X0,X1) = iProver_top
% 35.86/4.98      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_6032,plain,
% 35.86/4.98      ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_6026,c_3441]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_4,plain,
% 35.86/4.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 35.86/4.98      inference(cnf_transformation,[],[f81]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3446,plain,
% 35.86/4.98      ( r1_tarski(X0,X1) != iProver_top
% 35.86/4.98      | r2_hidden(X2,X0) != iProver_top
% 35.86/4.98      | r2_hidden(X2,X1) = iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_6649,plain,
% 35.86/4.98      ( r2_hidden(X0,u1_struct_0(sK8)) = iProver_top
% 35.86/4.98      | r2_hidden(X0,sK9) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_6032,c_3446]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_16,plain,
% 35.86/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.86/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.86/4.98      | ~ r2_hidden(sK3(X1,X2,X0),X0)
% 35.86/4.98      | ~ r2_hidden(sK3(X1,X2,X0),X2)
% 35.86/4.98      | X2 = X0 ),
% 35.86/4.98      inference(cnf_transformation,[],[f97]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_3436,plain,
% 35.86/4.98      ( X0 = X1
% 35.86/4.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(X2,X0,X1),X1) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(X2,X0,X1),X0) != iProver_top ),
% 35.86/4.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_10917,plain,
% 35.86/4.98      ( u1_struct_0(sK8) = X0
% 35.86/4.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.86/4.98      | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(X1)) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(X1,X0,u1_struct_0(sK8)),X0) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(X1,X0,u1_struct_0(sK8)),sK9) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_6649,c_3436]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_147636,plain,
% 35.86/4.98      ( u1_struct_0(sK8) = sK9
% 35.86/4.98      | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | r2_hidden(sK3(u1_struct_0(sK8),sK9,u1_struct_0(sK8)),sK9) != iProver_top ),
% 35.86/4.98      inference(superposition,[status(thm)],[c_145113,c_10917]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_147671,plain,
% 35.86/4.98      ( u1_struct_0(sK8) = sK9
% 35.86/4.98      | m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 35.86/4.98      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 35.86/4.98      inference(forward_subsumption_resolution,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_147636,c_145113]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_179567,plain,
% 35.86/4.98      ( m1_subset_1(u1_struct_0(sK8),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 35.86/4.98      inference(global_propositional_subsumption,
% 35.86/4.98                [status(thm)],
% 35.86/4.98                [c_11715,c_55,c_3578,c_145120,c_147671]) ).
% 35.86/4.98  
% 35.86/4.98  cnf(c_179572,plain,
% 35.86/4.98      ( $false ),
% 35.86/4.98      inference(forward_subsumption_resolution,[status(thm)],[c_179567,c_3463]) ).
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.86/4.98  
% 35.86/4.98  ------                               Statistics
% 35.86/4.98  
% 35.86/4.98  ------ General
% 35.86/4.98  
% 35.86/4.98  abstr_ref_over_cycles:                  0
% 35.86/4.98  abstr_ref_under_cycles:                 0
% 35.86/4.98  gc_basic_clause_elim:                   0
% 35.86/4.98  forced_gc_time:                         0
% 35.86/4.98  parsing_time:                           0.013
% 35.86/4.98  unif_index_cands_time:                  0.
% 35.86/4.98  unif_index_add_time:                    0.
% 35.86/4.98  orderings_time:                         0.
% 35.86/4.98  out_proof_time:                         0.026
% 35.86/4.98  total_time:                             4.333
% 35.86/4.98  num_of_symbols:                         60
% 35.86/4.98  num_of_terms:                           103567
% 35.86/4.98  
% 35.86/4.98  ------ Preprocessing
% 35.86/4.98  
% 35.86/4.98  num_of_splits:                          0
% 35.86/4.98  num_of_split_atoms:                     0
% 35.86/4.98  num_of_reused_defs:                     0
% 35.86/4.98  num_eq_ax_congr_red:                    55
% 35.86/4.98  num_of_sem_filtered_clauses:            1
% 35.86/4.98  num_of_subtypes:                        0
% 35.86/4.98  monotx_restored_types:                  0
% 35.86/4.98  sat_num_of_epr_types:                   0
% 35.86/4.98  sat_num_of_non_cyclic_types:            0
% 35.86/4.98  sat_guarded_non_collapsed_types:        0
% 35.86/4.98  num_pure_diseq_elim:                    0
% 35.86/4.98  simp_replaced_by:                       0
% 35.86/4.98  res_preprocessed:                       210
% 35.86/4.98  prep_upred:                             0
% 35.86/4.98  prep_unflattend:                        86
% 35.86/4.98  smt_new_axioms:                         0
% 35.86/4.98  pred_elim_cands:                        7
% 35.86/4.98  pred_elim:                              6
% 35.86/4.98  pred_elim_cl:                           7
% 35.86/4.98  pred_elim_cycles:                       12
% 35.86/4.98  merged_defs:                            10
% 35.86/4.98  merged_defs_ncl:                        0
% 35.86/4.98  bin_hyper_res:                          10
% 35.86/4.98  prep_cycles:                            4
% 35.86/4.98  pred_elim_time:                         0.028
% 35.86/4.98  splitting_time:                         0.
% 35.86/4.98  sem_filter_time:                        0.
% 35.86/4.98  monotx_time:                            0.001
% 35.86/4.98  subtype_inf_time:                       0.
% 35.86/4.98  
% 35.86/4.98  ------ Problem properties
% 35.86/4.98  
% 35.86/4.98  clauses:                                42
% 35.86/4.98  conjectures:                            3
% 35.86/4.98  epr:                                    9
% 35.86/4.98  horn:                                   27
% 35.86/4.98  ground:                                 8
% 35.86/4.98  unary:                                  9
% 35.86/4.98  binary:                                 8
% 35.86/4.98  lits:                                   113
% 35.86/4.98  lits_eq:                                12
% 35.86/4.98  fd_pure:                                0
% 35.86/4.98  fd_pseudo:                              0
% 35.86/4.98  fd_cond:                                3
% 35.86/4.98  fd_pseudo_cond:                         5
% 35.86/4.98  ac_symbols:                             0
% 35.86/4.98  
% 35.86/4.98  ------ Propositional Solver
% 35.86/4.98  
% 35.86/4.98  prop_solver_calls:                      49
% 35.86/4.98  prop_fast_solver_calls:                 5643
% 35.86/4.98  smt_solver_calls:                       0
% 35.86/4.98  smt_fast_solver_calls:                  0
% 35.86/4.98  prop_num_of_clauses:                    47657
% 35.86/4.98  prop_preprocess_simplified:             67482
% 35.86/4.98  prop_fo_subsumed:                       276
% 35.86/4.98  prop_solver_time:                       0.
% 35.86/4.98  smt_solver_time:                        0.
% 35.86/4.98  smt_fast_solver_time:                   0.
% 35.86/4.98  prop_fast_solver_time:                  0.
% 35.86/4.98  prop_unsat_core_time:                   0.
% 35.86/4.98  
% 35.86/4.98  ------ QBF
% 35.86/4.98  
% 35.86/4.98  qbf_q_res:                              0
% 35.86/4.98  qbf_num_tautologies:                    0
% 35.86/4.98  qbf_prep_cycles:                        0
% 35.86/4.98  
% 35.86/4.98  ------ BMC1
% 35.86/4.98  
% 35.86/4.98  bmc1_current_bound:                     -1
% 35.86/4.98  bmc1_last_solved_bound:                 -1
% 35.86/4.98  bmc1_unsat_core_size:                   -1
% 35.86/4.98  bmc1_unsat_core_parents_size:           -1
% 35.86/4.98  bmc1_merge_next_fun:                    0
% 35.86/4.98  bmc1_unsat_core_clauses_time:           0.
% 35.86/4.98  
% 35.86/4.98  ------ Instantiation
% 35.86/4.98  
% 35.86/4.98  inst_num_of_clauses:                    1995
% 35.86/4.98  inst_num_in_passive:                    1159
% 35.86/4.98  inst_num_in_active:                     2904
% 35.86/4.98  inst_num_in_unprocessed:                21
% 35.86/4.98  inst_num_of_loops:                      3899
% 35.86/4.98  inst_num_of_learning_restarts:          1
% 35.86/4.98  inst_num_moves_active_passive:          992
% 35.86/4.98  inst_lit_activity:                      0
% 35.86/4.98  inst_lit_activity_moves:                1
% 35.86/4.98  inst_num_tautologies:                   0
% 35.86/4.98  inst_num_prop_implied:                  0
% 35.86/4.98  inst_num_existing_simplified:           0
% 35.86/4.98  inst_num_eq_res_simplified:             0
% 35.86/4.98  inst_num_child_elim:                    0
% 35.86/4.98  inst_num_of_dismatching_blockings:      8433
% 35.86/4.98  inst_num_of_non_proper_insts:           10073
% 35.86/4.98  inst_num_of_duplicates:                 0
% 35.86/4.98  inst_inst_num_from_inst_to_res:         0
% 35.86/4.98  inst_dismatching_checking_time:         0.
% 35.86/4.98  
% 35.86/4.98  ------ Resolution
% 35.86/4.98  
% 35.86/4.98  res_num_of_clauses:                     59
% 35.86/4.98  res_num_in_passive:                     59
% 35.86/4.98  res_num_in_active:                      0
% 35.86/4.98  res_num_of_loops:                       214
% 35.86/4.98  res_forward_subset_subsumed:            1190
% 35.86/4.98  res_backward_subset_subsumed:           0
% 35.86/4.98  res_forward_subsumed:                   0
% 35.86/4.98  res_backward_subsumed:                  0
% 35.86/4.98  res_forward_subsumption_resolution:     6
% 35.86/4.98  res_backward_subsumption_resolution:    0
% 35.86/4.98  res_clause_to_clause_subsumption:       69047
% 35.86/4.98  res_orphan_elimination:                 0
% 35.86/4.98  res_tautology_del:                      365
% 35.86/4.98  res_num_eq_res_simplified:              0
% 35.86/4.98  res_num_sel_changes:                    0
% 35.86/4.98  res_moves_from_active_to_pass:          0
% 35.86/4.98  
% 35.86/4.98  ------ Superposition
% 35.86/4.98  
% 35.86/4.98  sup_time_total:                         0.
% 35.86/4.98  sup_time_generating:                    0.
% 35.86/4.98  sup_time_sim_full:                      0.
% 35.86/4.98  sup_time_sim_immed:                     0.
% 35.86/4.98  
% 35.86/4.98  sup_num_of_clauses:                     5914
% 35.86/4.98  sup_num_in_active:                      725
% 35.86/4.98  sup_num_in_passive:                     5189
% 35.86/4.98  sup_num_of_loops:                       778
% 35.86/4.98  sup_fw_superposition:                   3995
% 35.86/4.98  sup_bw_superposition:                   4646
% 35.86/4.98  sup_immediate_simplified:               1491
% 35.86/4.98  sup_given_eliminated:                   1
% 35.86/4.98  comparisons_done:                       0
% 35.86/4.98  comparisons_avoided:                    3
% 35.86/4.98  
% 35.86/4.98  ------ Simplifications
% 35.86/4.98  
% 35.86/4.98  
% 35.86/4.98  sim_fw_subset_subsumed:                 797
% 35.86/4.98  sim_bw_subset_subsumed:                 273
% 35.86/4.98  sim_fw_subsumed:                        568
% 35.86/4.98  sim_bw_subsumed:                        82
% 35.86/4.98  sim_fw_subsumption_res:                 24
% 35.86/4.98  sim_bw_subsumption_res:                 11
% 35.86/4.98  sim_tautology_del:                      120
% 35.86/4.98  sim_eq_tautology_del:                   94
% 35.86/4.98  sim_eq_res_simp:                        3
% 35.86/4.98  sim_fw_demodulated:                     3
% 35.86/4.98  sim_bw_demodulated:                     0
% 35.86/4.98  sim_light_normalised:                   32
% 35.86/4.98  sim_joinable_taut:                      0
% 35.86/4.98  sim_joinable_simp:                      0
% 35.86/4.98  sim_ac_normalised:                      0
% 35.86/4.98  sim_smt_subsumption:                    0
% 35.86/4.98  
%------------------------------------------------------------------------------
