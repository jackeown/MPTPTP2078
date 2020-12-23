%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:25 EST 2020

% Result     : Theorem 15.06s
% Output     : CNFRefutation 15.06s
% Verified   : 
% Statistics : Number of formulae       :  292 (4115 expanded)
%              Number of clauses        :  180 (1125 expanded)
%              Number of leaves         :   30 ( 773 expanded)
%              Depth                    :   42
%              Number of atoms          : 1088 (29651 expanded)
%              Number of equality atoms :  278 (1513 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

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
    inference(flattening,[],[f46])).

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
    inference(nnf_transformation,[],[f47])).

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
     => ( ( r2_hidden(k3_yellow_0(X0),sK6)
          | ~ v1_subset_1(sK6,u1_struct_0(X0)) )
        & ( ~ r2_hidden(k3_yellow_0(X0),sK6)
          | v1_subset_1(sK6,u1_struct_0(X0)) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
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

fof(f74,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f71,f73,f72])).

fof(f115,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f118,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f74])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f120,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f74])).

fof(f14,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_lattice3(X0,X1,sK2(X0,X1,X2))
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f103,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,(
    v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f112,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f113,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f18,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f43])).

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
    inference(nnf_transformation,[],[f44])).

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
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,X2,sK4(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
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
            & r1_orders_2(X0,sK3(X0,X1),X3)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f65,f67,f66])).

fof(f104,plain,(
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

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f117,plain,(
    v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f74])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f110,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f119,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f74])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f116,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f74])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2912,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2906,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4434,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_2906])).

cnf(c_20,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_843,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_42])).

cnf(c_844,plain,
    ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2901,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4109,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2904])).

cnf(c_26,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_834,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_42])).

cnf(c_835,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_2888,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_35,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_446,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_35,c_358])).

cnf(c_37,negated_conjecture,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_361,plain,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_37])).

cnf(c_628,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_446,c_361])).

cnf(c_629,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | u1_struct_0(sK5) = sK6 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_2898,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_52,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_630,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_3290,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3291,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3290])).

cnf(c_5100,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
    | u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2898,c_52,c_630,c_3291])).

cnf(c_5101,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_5100])).

cnf(c_24,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_26])).

cnf(c_271,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_28,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_43,negated_conjecture,
    ( v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_612,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_43])).

cnf(c_613,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_44,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_78,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_yellow_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_615,plain,
    ( r1_yellow_0(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_45,c_44,c_43,c_42,c_78])).

cnf(c_662,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_615])).

cnf(c_663,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_667,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_42])).

cnf(c_668,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_2896,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_3030,plain,
    ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2896,c_844])).

cnf(c_34,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_787,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_42])).

cnf(c_788,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_804,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_788,c_14])).

cnf(c_2891,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_4383,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2891])).

cnf(c_40,negated_conjecture,
    ( v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1024,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK6 != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_804])).

cnf(c_1025,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_39])).

cnf(c_1028,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(renaming,[status(thm)],[c_1027])).

cnf(c_1029,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1028])).

cnf(c_4730,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_1029])).

cnf(c_4739,plain,
    ( r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_4730])).

cnf(c_5109,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5101,c_4739])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2907,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4107,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_2904])).

cnf(c_17,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_884,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_42])).

cnf(c_885,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK1(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_2885,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK1(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2902,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4049,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,sK1(sK5,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2885,c_2902])).

cnf(c_5246,plain,
    ( r2_lattice3(sK5,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4107,c_4049])).

cnf(c_15643,plain,
    ( u1_struct_0(sK5) = sK6
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5109,c_5246])).

cnf(c_15655,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2888,c_15643])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16549,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(sK6,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15655,c_2911])).

cnf(c_18010,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK6,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16549,c_2911])).

cnf(c_23897,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
    | r1_tarski(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_18010])).

cnf(c_3555,plain,
    ( r2_hidden(sK0(X0,sK6),X0)
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6027,plain,
    ( r2_hidden(sK0(sK6,sK6),sK6)
    | r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_3555])).

cnf(c_6029,plain,
    ( r2_hidden(sK0(sK6,sK6),sK6) = iProver_top
    | r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6027])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3556,plain,
    ( ~ r2_hidden(sK0(X0,sK6),sK6)
    | r1_tarski(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6028,plain,
    ( ~ r2_hidden(sK0(sK6,sK6),sK6)
    | r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_6031,plain,
    ( r2_hidden(sK0(sK6,sK6),sK6) != iProver_top
    | r1_tarski(sK6,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6028])).

cnf(c_24191,plain,
    ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
    | u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23897,c_6029,c_6031])).

cnf(c_24192,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_24191])).

cnf(c_24200,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24192,c_2911])).

cnf(c_36,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_56,plain,
    ( ~ v1_subset_1(sK5,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_59,plain,
    ( v1_subset_1(sK5,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_81,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_126,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK5))
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_143,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2107,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2121,plain,
    ( k3_yellow_0(sK5) = k3_yellow_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_38,negated_conjecture,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_359,plain,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_38])).

cnf(c_641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_359])).

cnf(c_642,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_2897,plain,
    ( sK6 != u1_struct_0(sK5)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2908,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2928,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2908,c_6])).

cnf(c_3021,plain,
    ( u1_struct_0(sK5) != sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2897,c_2928])).

cnf(c_3132,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) != sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3021])).

cnf(c_2097,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3367,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_41])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,sK6)
    | r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_6385,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_2102,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3316,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X0 != k3_yellow_0(sK5)
    | X1 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_3600,plain,
    ( m1_subset_1(k3_yellow_0(X0),X1)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X1 != u1_struct_0(sK5)
    | k3_yellow_0(X0) != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3316])).

cnf(c_10647,plain,
    ( m1_subset_1(k3_yellow_0(X0),sK6)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | k3_yellow_0(X0) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3600])).

cnf(c_10651,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | m1_subset_1(k3_yellow_0(sK5),sK6)
    | k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10647])).

cnf(c_2098,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3610,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_4937,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3610])).

cnf(c_25472,plain,
    ( u1_struct_0(sK5) != sK6
    | sK6 = u1_struct_0(sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4937])).

cnf(c_25487,plain,
    ( r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24200,c_42,c_56,c_59,c_81,c_126,c_143,c_2121,c_3132,c_3367,c_6385,c_10651,c_25472])).

cnf(c_25498,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_25487,c_2906])).

cnf(c_31,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X1,X0),X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_944,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK3(X1,X0),X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_42])).

cnf(c_945,plain,
    ( v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK3(sK5,X0),X0) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_2881,plain,
    ( v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK3(sK5,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_25627,plain,
    ( v13_waybel_0(k1_yellow_0(sK5,X0),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k1_yellow_0(sK5,X0)),k1_yellow_0(sK5,X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25498,c_2881])).

cnf(c_27093,plain,
    ( v13_waybel_0(k1_yellow_0(sK5,k1_xboole_0),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_25627])).

cnf(c_27143,plain,
    ( v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27093,c_844])).

cnf(c_33,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_914,plain,
    ( v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_42])).

cnf(c_915,plain,
    ( v13_waybel_0(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_914])).

cnf(c_2883,plain,
    ( v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_19,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_848,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_42])).

cnf(c_849,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ r2_lattice3(sK5,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_2887,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | r2_lattice3(sK5,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_3841,plain,
    ( r1_orders_2(sK5,sK3(sK5,X0),X1) = iProver_top
    | r2_lattice3(sK5,X2,X1) != iProver_top
    | v13_waybel_0(X0,sK5) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK3(sK5,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_2887])).

cnf(c_27171,plain,
    ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
    | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27143,c_3841])).

cnf(c_25605,plain,
    ( m1_subset_1(k3_yellow_0(sK5),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_25498])).

cnf(c_29069,plain,
    ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
    | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27171,c_25605])).

cnf(c_29077,plain,
    ( r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
    | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),sK6) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29069,c_4730])).

cnf(c_49,plain,
    ( l1_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_80,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_82,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top
    | l1_orders_2(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_6386,plain,
    ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6385])).

cnf(c_10650,plain,
    ( k3_yellow_0(X0) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5)
    | m1_subset_1(k3_yellow_0(X0),sK6) = iProver_top
    | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10647])).

cnf(c_10652,plain,
    ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5)
    | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10650])).

cnf(c_30633,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29077,c_42,c_56,c_59,c_81,c_126,c_143,c_2121,c_3132,c_3367,c_6385,c_10651,c_15643,c_25472])).

cnf(c_30650,plain,
    ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4434,c_30633])).

cnf(c_2913,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_65331,plain,
    ( r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_30650,c_2913])).

cnf(c_827,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_828,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_2889,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_30641,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2889,c_30633])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3604,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4603,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),sK6)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | sK6 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3604])).

cnf(c_4604,plain,
    ( sK6 = u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4603])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3524,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3527,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3524])).

cnf(c_3285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3523,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3285])).

cnf(c_3525,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3523])).

cnf(c_643,plain,
    ( sK6 != u1_struct_0(sK5)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65331,c_30641,c_4604,c_3527,c_3525,c_3291,c_643,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.06/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/2.50  
% 15.06/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.06/2.50  
% 15.06/2.50  ------  iProver source info
% 15.06/2.50  
% 15.06/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.06/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.06/2.50  git: non_committed_changes: false
% 15.06/2.50  git: last_make_outside_of_git: false
% 15.06/2.50  
% 15.06/2.50  ------ 
% 15.06/2.50  
% 15.06/2.50  ------ Input Options
% 15.06/2.50  
% 15.06/2.50  --out_options                           all
% 15.06/2.50  --tptp_safe_out                         true
% 15.06/2.50  --problem_path                          ""
% 15.06/2.50  --include_path                          ""
% 15.06/2.50  --clausifier                            res/vclausify_rel
% 15.06/2.50  --clausifier_options                    --mode clausify
% 15.06/2.50  --stdin                                 false
% 15.06/2.50  --stats_out                             all
% 15.06/2.50  
% 15.06/2.50  ------ General Options
% 15.06/2.50  
% 15.06/2.50  --fof                                   false
% 15.06/2.50  --time_out_real                         305.
% 15.06/2.50  --time_out_virtual                      -1.
% 15.06/2.50  --symbol_type_check                     false
% 15.06/2.50  --clausify_out                          false
% 15.06/2.50  --sig_cnt_out                           false
% 15.06/2.50  --trig_cnt_out                          false
% 15.06/2.50  --trig_cnt_out_tolerance                1.
% 15.06/2.50  --trig_cnt_out_sk_spl                   false
% 15.06/2.50  --abstr_cl_out                          false
% 15.06/2.50  
% 15.06/2.50  ------ Global Options
% 15.06/2.50  
% 15.06/2.50  --schedule                              default
% 15.06/2.50  --add_important_lit                     false
% 15.06/2.50  --prop_solver_per_cl                    1000
% 15.06/2.50  --min_unsat_core                        false
% 15.06/2.50  --soft_assumptions                      false
% 15.06/2.50  --soft_lemma_size                       3
% 15.06/2.50  --prop_impl_unit_size                   0
% 15.06/2.50  --prop_impl_unit                        []
% 15.06/2.50  --share_sel_clauses                     true
% 15.06/2.50  --reset_solvers                         false
% 15.06/2.50  --bc_imp_inh                            [conj_cone]
% 15.06/2.50  --conj_cone_tolerance                   3.
% 15.06/2.50  --extra_neg_conj                        none
% 15.06/2.50  --large_theory_mode                     true
% 15.06/2.50  --prolific_symb_bound                   200
% 15.06/2.50  --lt_threshold                          2000
% 15.06/2.50  --clause_weak_htbl                      true
% 15.06/2.50  --gc_record_bc_elim                     false
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing Options
% 15.06/2.50  
% 15.06/2.50  --preprocessing_flag                    true
% 15.06/2.50  --time_out_prep_mult                    0.1
% 15.06/2.50  --splitting_mode                        input
% 15.06/2.50  --splitting_grd                         true
% 15.06/2.50  --splitting_cvd                         false
% 15.06/2.50  --splitting_cvd_svl                     false
% 15.06/2.50  --splitting_nvd                         32
% 15.06/2.50  --sub_typing                            true
% 15.06/2.50  --prep_gs_sim                           true
% 15.06/2.50  --prep_unflatten                        true
% 15.06/2.50  --prep_res_sim                          true
% 15.06/2.50  --prep_upred                            true
% 15.06/2.50  --prep_sem_filter                       exhaustive
% 15.06/2.50  --prep_sem_filter_out                   false
% 15.06/2.50  --pred_elim                             true
% 15.06/2.50  --res_sim_input                         true
% 15.06/2.50  --eq_ax_congr_red                       true
% 15.06/2.50  --pure_diseq_elim                       true
% 15.06/2.50  --brand_transform                       false
% 15.06/2.50  --non_eq_to_eq                          false
% 15.06/2.50  --prep_def_merge                        true
% 15.06/2.50  --prep_def_merge_prop_impl              false
% 15.06/2.50  --prep_def_merge_mbd                    true
% 15.06/2.50  --prep_def_merge_tr_red                 false
% 15.06/2.50  --prep_def_merge_tr_cl                  false
% 15.06/2.50  --smt_preprocessing                     true
% 15.06/2.50  --smt_ac_axioms                         fast
% 15.06/2.50  --preprocessed_out                      false
% 15.06/2.50  --preprocessed_stats                    false
% 15.06/2.50  
% 15.06/2.50  ------ Abstraction refinement Options
% 15.06/2.50  
% 15.06/2.50  --abstr_ref                             []
% 15.06/2.50  --abstr_ref_prep                        false
% 15.06/2.50  --abstr_ref_until_sat                   false
% 15.06/2.50  --abstr_ref_sig_restrict                funpre
% 15.06/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.06/2.50  --abstr_ref_under                       []
% 15.06/2.50  
% 15.06/2.50  ------ SAT Options
% 15.06/2.50  
% 15.06/2.50  --sat_mode                              false
% 15.06/2.50  --sat_fm_restart_options                ""
% 15.06/2.50  --sat_gr_def                            false
% 15.06/2.50  --sat_epr_types                         true
% 15.06/2.50  --sat_non_cyclic_types                  false
% 15.06/2.50  --sat_finite_models                     false
% 15.06/2.50  --sat_fm_lemmas                         false
% 15.06/2.50  --sat_fm_prep                           false
% 15.06/2.50  --sat_fm_uc_incr                        true
% 15.06/2.50  --sat_out_model                         small
% 15.06/2.50  --sat_out_clauses                       false
% 15.06/2.50  
% 15.06/2.50  ------ QBF Options
% 15.06/2.50  
% 15.06/2.50  --qbf_mode                              false
% 15.06/2.50  --qbf_elim_univ                         false
% 15.06/2.50  --qbf_dom_inst                          none
% 15.06/2.50  --qbf_dom_pre_inst                      false
% 15.06/2.50  --qbf_sk_in                             false
% 15.06/2.50  --qbf_pred_elim                         true
% 15.06/2.50  --qbf_split                             512
% 15.06/2.50  
% 15.06/2.50  ------ BMC1 Options
% 15.06/2.50  
% 15.06/2.50  --bmc1_incremental                      false
% 15.06/2.50  --bmc1_axioms                           reachable_all
% 15.06/2.50  --bmc1_min_bound                        0
% 15.06/2.50  --bmc1_max_bound                        -1
% 15.06/2.50  --bmc1_max_bound_default                -1
% 15.06/2.50  --bmc1_symbol_reachability              true
% 15.06/2.50  --bmc1_property_lemmas                  false
% 15.06/2.50  --bmc1_k_induction                      false
% 15.06/2.50  --bmc1_non_equiv_states                 false
% 15.06/2.50  --bmc1_deadlock                         false
% 15.06/2.50  --bmc1_ucm                              false
% 15.06/2.50  --bmc1_add_unsat_core                   none
% 15.06/2.50  --bmc1_unsat_core_children              false
% 15.06/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.06/2.50  --bmc1_out_stat                         full
% 15.06/2.50  --bmc1_ground_init                      false
% 15.06/2.50  --bmc1_pre_inst_next_state              false
% 15.06/2.50  --bmc1_pre_inst_state                   false
% 15.06/2.50  --bmc1_pre_inst_reach_state             false
% 15.06/2.50  --bmc1_out_unsat_core                   false
% 15.06/2.50  --bmc1_aig_witness_out                  false
% 15.06/2.50  --bmc1_verbose                          false
% 15.06/2.50  --bmc1_dump_clauses_tptp                false
% 15.06/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.06/2.50  --bmc1_dump_file                        -
% 15.06/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.06/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.06/2.50  --bmc1_ucm_extend_mode                  1
% 15.06/2.50  --bmc1_ucm_init_mode                    2
% 15.06/2.50  --bmc1_ucm_cone_mode                    none
% 15.06/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.06/2.50  --bmc1_ucm_relax_model                  4
% 15.06/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.06/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.06/2.50  --bmc1_ucm_layered_model                none
% 15.06/2.50  --bmc1_ucm_max_lemma_size               10
% 15.06/2.50  
% 15.06/2.50  ------ AIG Options
% 15.06/2.50  
% 15.06/2.50  --aig_mode                              false
% 15.06/2.50  
% 15.06/2.50  ------ Instantiation Options
% 15.06/2.50  
% 15.06/2.50  --instantiation_flag                    true
% 15.06/2.50  --inst_sos_flag                         false
% 15.06/2.50  --inst_sos_phase                        true
% 15.06/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.06/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.06/2.50  --inst_lit_sel_side                     num_symb
% 15.06/2.50  --inst_solver_per_active                1400
% 15.06/2.50  --inst_solver_calls_frac                1.
% 15.06/2.50  --inst_passive_queue_type               priority_queues
% 15.06/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.06/2.50  --inst_passive_queues_freq              [25;2]
% 15.06/2.50  --inst_dismatching                      true
% 15.06/2.50  --inst_eager_unprocessed_to_passive     true
% 15.06/2.50  --inst_prop_sim_given                   true
% 15.06/2.50  --inst_prop_sim_new                     false
% 15.06/2.50  --inst_subs_new                         false
% 15.06/2.50  --inst_eq_res_simp                      false
% 15.06/2.50  --inst_subs_given                       false
% 15.06/2.50  --inst_orphan_elimination               true
% 15.06/2.50  --inst_learning_loop_flag               true
% 15.06/2.50  --inst_learning_start                   3000
% 15.06/2.50  --inst_learning_factor                  2
% 15.06/2.50  --inst_start_prop_sim_after_learn       3
% 15.06/2.50  --inst_sel_renew                        solver
% 15.06/2.50  --inst_lit_activity_flag                true
% 15.06/2.50  --inst_restr_to_given                   false
% 15.06/2.50  --inst_activity_threshold               500
% 15.06/2.50  --inst_out_proof                        true
% 15.06/2.50  
% 15.06/2.50  ------ Resolution Options
% 15.06/2.50  
% 15.06/2.50  --resolution_flag                       true
% 15.06/2.50  --res_lit_sel                           adaptive
% 15.06/2.50  --res_lit_sel_side                      none
% 15.06/2.50  --res_ordering                          kbo
% 15.06/2.50  --res_to_prop_solver                    active
% 15.06/2.50  --res_prop_simpl_new                    false
% 15.06/2.50  --res_prop_simpl_given                  true
% 15.06/2.50  --res_passive_queue_type                priority_queues
% 15.06/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.06/2.50  --res_passive_queues_freq               [15;5]
% 15.06/2.50  --res_forward_subs                      full
% 15.06/2.50  --res_backward_subs                     full
% 15.06/2.50  --res_forward_subs_resolution           true
% 15.06/2.50  --res_backward_subs_resolution          true
% 15.06/2.50  --res_orphan_elimination                true
% 15.06/2.50  --res_time_limit                        2.
% 15.06/2.50  --res_out_proof                         true
% 15.06/2.50  
% 15.06/2.50  ------ Superposition Options
% 15.06/2.50  
% 15.06/2.50  --superposition_flag                    true
% 15.06/2.50  --sup_passive_queue_type                priority_queues
% 15.06/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.06/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.06/2.50  --demod_completeness_check              fast
% 15.06/2.50  --demod_use_ground                      true
% 15.06/2.50  --sup_to_prop_solver                    passive
% 15.06/2.50  --sup_prop_simpl_new                    true
% 15.06/2.50  --sup_prop_simpl_given                  true
% 15.06/2.50  --sup_fun_splitting                     false
% 15.06/2.50  --sup_smt_interval                      50000
% 15.06/2.50  
% 15.06/2.50  ------ Superposition Simplification Setup
% 15.06/2.50  
% 15.06/2.50  --sup_indices_passive                   []
% 15.06/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.06/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_full_bw                           [BwDemod]
% 15.06/2.50  --sup_immed_triv                        [TrivRules]
% 15.06/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.06/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_immed_bw_main                     []
% 15.06/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.06/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.06/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.06/2.50  
% 15.06/2.50  ------ Combination Options
% 15.06/2.50  
% 15.06/2.50  --comb_res_mult                         3
% 15.06/2.50  --comb_sup_mult                         2
% 15.06/2.50  --comb_inst_mult                        10
% 15.06/2.50  
% 15.06/2.50  ------ Debug Options
% 15.06/2.50  
% 15.06/2.50  --dbg_backtrace                         false
% 15.06/2.50  --dbg_dump_prop_clauses                 false
% 15.06/2.50  --dbg_dump_prop_clauses_file            -
% 15.06/2.50  --dbg_out_stat                          false
% 15.06/2.50  ------ Parsing...
% 15.06/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.06/2.50  ------ Proving...
% 15.06/2.50  ------ Problem Properties 
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  clauses                                 36
% 15.06/2.50  conjectures                             2
% 15.06/2.50  EPR                                     7
% 15.06/2.50  Horn                                    26
% 15.06/2.50  unary                                   10
% 15.06/2.50  binary                                  7
% 15.06/2.50  lits                                    89
% 15.06/2.50  lits eq                                 8
% 15.06/2.50  fd_pure                                 0
% 15.06/2.50  fd_pseudo                               0
% 15.06/2.50  fd_cond                                 3
% 15.06/2.50  fd_pseudo_cond                          1
% 15.06/2.50  AC symbols                              0
% 15.06/2.50  
% 15.06/2.50  ------ Schedule dynamic 5 is on 
% 15.06/2.50  
% 15.06/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  ------ 
% 15.06/2.50  Current options:
% 15.06/2.50  ------ 
% 15.06/2.50  
% 15.06/2.50  ------ Input Options
% 15.06/2.50  
% 15.06/2.50  --out_options                           all
% 15.06/2.50  --tptp_safe_out                         true
% 15.06/2.50  --problem_path                          ""
% 15.06/2.50  --include_path                          ""
% 15.06/2.50  --clausifier                            res/vclausify_rel
% 15.06/2.50  --clausifier_options                    --mode clausify
% 15.06/2.50  --stdin                                 false
% 15.06/2.50  --stats_out                             all
% 15.06/2.50  
% 15.06/2.50  ------ General Options
% 15.06/2.50  
% 15.06/2.50  --fof                                   false
% 15.06/2.50  --time_out_real                         305.
% 15.06/2.50  --time_out_virtual                      -1.
% 15.06/2.50  --symbol_type_check                     false
% 15.06/2.50  --clausify_out                          false
% 15.06/2.50  --sig_cnt_out                           false
% 15.06/2.50  --trig_cnt_out                          false
% 15.06/2.50  --trig_cnt_out_tolerance                1.
% 15.06/2.50  --trig_cnt_out_sk_spl                   false
% 15.06/2.50  --abstr_cl_out                          false
% 15.06/2.50  
% 15.06/2.50  ------ Global Options
% 15.06/2.50  
% 15.06/2.50  --schedule                              default
% 15.06/2.50  --add_important_lit                     false
% 15.06/2.50  --prop_solver_per_cl                    1000
% 15.06/2.50  --min_unsat_core                        false
% 15.06/2.50  --soft_assumptions                      false
% 15.06/2.50  --soft_lemma_size                       3
% 15.06/2.50  --prop_impl_unit_size                   0
% 15.06/2.50  --prop_impl_unit                        []
% 15.06/2.50  --share_sel_clauses                     true
% 15.06/2.50  --reset_solvers                         false
% 15.06/2.50  --bc_imp_inh                            [conj_cone]
% 15.06/2.50  --conj_cone_tolerance                   3.
% 15.06/2.50  --extra_neg_conj                        none
% 15.06/2.50  --large_theory_mode                     true
% 15.06/2.50  --prolific_symb_bound                   200
% 15.06/2.50  --lt_threshold                          2000
% 15.06/2.50  --clause_weak_htbl                      true
% 15.06/2.50  --gc_record_bc_elim                     false
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing Options
% 15.06/2.50  
% 15.06/2.50  --preprocessing_flag                    true
% 15.06/2.50  --time_out_prep_mult                    0.1
% 15.06/2.50  --splitting_mode                        input
% 15.06/2.50  --splitting_grd                         true
% 15.06/2.50  --splitting_cvd                         false
% 15.06/2.50  --splitting_cvd_svl                     false
% 15.06/2.50  --splitting_nvd                         32
% 15.06/2.50  --sub_typing                            true
% 15.06/2.50  --prep_gs_sim                           true
% 15.06/2.50  --prep_unflatten                        true
% 15.06/2.50  --prep_res_sim                          true
% 15.06/2.50  --prep_upred                            true
% 15.06/2.50  --prep_sem_filter                       exhaustive
% 15.06/2.50  --prep_sem_filter_out                   false
% 15.06/2.50  --pred_elim                             true
% 15.06/2.50  --res_sim_input                         true
% 15.06/2.50  --eq_ax_congr_red                       true
% 15.06/2.50  --pure_diseq_elim                       true
% 15.06/2.50  --brand_transform                       false
% 15.06/2.50  --non_eq_to_eq                          false
% 15.06/2.50  --prep_def_merge                        true
% 15.06/2.50  --prep_def_merge_prop_impl              false
% 15.06/2.50  --prep_def_merge_mbd                    true
% 15.06/2.50  --prep_def_merge_tr_red                 false
% 15.06/2.50  --prep_def_merge_tr_cl                  false
% 15.06/2.50  --smt_preprocessing                     true
% 15.06/2.50  --smt_ac_axioms                         fast
% 15.06/2.50  --preprocessed_out                      false
% 15.06/2.50  --preprocessed_stats                    false
% 15.06/2.50  
% 15.06/2.50  ------ Abstraction refinement Options
% 15.06/2.50  
% 15.06/2.50  --abstr_ref                             []
% 15.06/2.50  --abstr_ref_prep                        false
% 15.06/2.50  --abstr_ref_until_sat                   false
% 15.06/2.50  --abstr_ref_sig_restrict                funpre
% 15.06/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.06/2.50  --abstr_ref_under                       []
% 15.06/2.50  
% 15.06/2.50  ------ SAT Options
% 15.06/2.50  
% 15.06/2.50  --sat_mode                              false
% 15.06/2.50  --sat_fm_restart_options                ""
% 15.06/2.50  --sat_gr_def                            false
% 15.06/2.50  --sat_epr_types                         true
% 15.06/2.50  --sat_non_cyclic_types                  false
% 15.06/2.50  --sat_finite_models                     false
% 15.06/2.50  --sat_fm_lemmas                         false
% 15.06/2.50  --sat_fm_prep                           false
% 15.06/2.50  --sat_fm_uc_incr                        true
% 15.06/2.50  --sat_out_model                         small
% 15.06/2.50  --sat_out_clauses                       false
% 15.06/2.50  
% 15.06/2.50  ------ QBF Options
% 15.06/2.50  
% 15.06/2.50  --qbf_mode                              false
% 15.06/2.50  --qbf_elim_univ                         false
% 15.06/2.50  --qbf_dom_inst                          none
% 15.06/2.50  --qbf_dom_pre_inst                      false
% 15.06/2.50  --qbf_sk_in                             false
% 15.06/2.50  --qbf_pred_elim                         true
% 15.06/2.50  --qbf_split                             512
% 15.06/2.50  
% 15.06/2.50  ------ BMC1 Options
% 15.06/2.50  
% 15.06/2.50  --bmc1_incremental                      false
% 15.06/2.50  --bmc1_axioms                           reachable_all
% 15.06/2.50  --bmc1_min_bound                        0
% 15.06/2.50  --bmc1_max_bound                        -1
% 15.06/2.50  --bmc1_max_bound_default                -1
% 15.06/2.50  --bmc1_symbol_reachability              true
% 15.06/2.50  --bmc1_property_lemmas                  false
% 15.06/2.50  --bmc1_k_induction                      false
% 15.06/2.50  --bmc1_non_equiv_states                 false
% 15.06/2.50  --bmc1_deadlock                         false
% 15.06/2.50  --bmc1_ucm                              false
% 15.06/2.50  --bmc1_add_unsat_core                   none
% 15.06/2.50  --bmc1_unsat_core_children              false
% 15.06/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.06/2.50  --bmc1_out_stat                         full
% 15.06/2.50  --bmc1_ground_init                      false
% 15.06/2.50  --bmc1_pre_inst_next_state              false
% 15.06/2.50  --bmc1_pre_inst_state                   false
% 15.06/2.50  --bmc1_pre_inst_reach_state             false
% 15.06/2.50  --bmc1_out_unsat_core                   false
% 15.06/2.50  --bmc1_aig_witness_out                  false
% 15.06/2.50  --bmc1_verbose                          false
% 15.06/2.50  --bmc1_dump_clauses_tptp                false
% 15.06/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.06/2.50  --bmc1_dump_file                        -
% 15.06/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.06/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.06/2.50  --bmc1_ucm_extend_mode                  1
% 15.06/2.50  --bmc1_ucm_init_mode                    2
% 15.06/2.50  --bmc1_ucm_cone_mode                    none
% 15.06/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.06/2.50  --bmc1_ucm_relax_model                  4
% 15.06/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.06/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.06/2.50  --bmc1_ucm_layered_model                none
% 15.06/2.50  --bmc1_ucm_max_lemma_size               10
% 15.06/2.50  
% 15.06/2.50  ------ AIG Options
% 15.06/2.50  
% 15.06/2.50  --aig_mode                              false
% 15.06/2.50  
% 15.06/2.50  ------ Instantiation Options
% 15.06/2.50  
% 15.06/2.50  --instantiation_flag                    true
% 15.06/2.50  --inst_sos_flag                         false
% 15.06/2.50  --inst_sos_phase                        true
% 15.06/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.06/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.06/2.50  --inst_lit_sel_side                     none
% 15.06/2.50  --inst_solver_per_active                1400
% 15.06/2.50  --inst_solver_calls_frac                1.
% 15.06/2.50  --inst_passive_queue_type               priority_queues
% 15.06/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.06/2.50  --inst_passive_queues_freq              [25;2]
% 15.06/2.50  --inst_dismatching                      true
% 15.06/2.50  --inst_eager_unprocessed_to_passive     true
% 15.06/2.50  --inst_prop_sim_given                   true
% 15.06/2.50  --inst_prop_sim_new                     false
% 15.06/2.50  --inst_subs_new                         false
% 15.06/2.50  --inst_eq_res_simp                      false
% 15.06/2.50  --inst_subs_given                       false
% 15.06/2.50  --inst_orphan_elimination               true
% 15.06/2.50  --inst_learning_loop_flag               true
% 15.06/2.50  --inst_learning_start                   3000
% 15.06/2.50  --inst_learning_factor                  2
% 15.06/2.50  --inst_start_prop_sim_after_learn       3
% 15.06/2.50  --inst_sel_renew                        solver
% 15.06/2.50  --inst_lit_activity_flag                true
% 15.06/2.50  --inst_restr_to_given                   false
% 15.06/2.50  --inst_activity_threshold               500
% 15.06/2.50  --inst_out_proof                        true
% 15.06/2.50  
% 15.06/2.50  ------ Resolution Options
% 15.06/2.50  
% 15.06/2.50  --resolution_flag                       false
% 15.06/2.50  --res_lit_sel                           adaptive
% 15.06/2.50  --res_lit_sel_side                      none
% 15.06/2.50  --res_ordering                          kbo
% 15.06/2.50  --res_to_prop_solver                    active
% 15.06/2.50  --res_prop_simpl_new                    false
% 15.06/2.50  --res_prop_simpl_given                  true
% 15.06/2.50  --res_passive_queue_type                priority_queues
% 15.06/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.06/2.50  --res_passive_queues_freq               [15;5]
% 15.06/2.50  --res_forward_subs                      full
% 15.06/2.50  --res_backward_subs                     full
% 15.06/2.50  --res_forward_subs_resolution           true
% 15.06/2.50  --res_backward_subs_resolution          true
% 15.06/2.50  --res_orphan_elimination                true
% 15.06/2.50  --res_time_limit                        2.
% 15.06/2.50  --res_out_proof                         true
% 15.06/2.50  
% 15.06/2.50  ------ Superposition Options
% 15.06/2.50  
% 15.06/2.50  --superposition_flag                    true
% 15.06/2.50  --sup_passive_queue_type                priority_queues
% 15.06/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.06/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.06/2.50  --demod_completeness_check              fast
% 15.06/2.50  --demod_use_ground                      true
% 15.06/2.50  --sup_to_prop_solver                    passive
% 15.06/2.50  --sup_prop_simpl_new                    true
% 15.06/2.50  --sup_prop_simpl_given                  true
% 15.06/2.50  --sup_fun_splitting                     false
% 15.06/2.50  --sup_smt_interval                      50000
% 15.06/2.50  
% 15.06/2.50  ------ Superposition Simplification Setup
% 15.06/2.50  
% 15.06/2.50  --sup_indices_passive                   []
% 15.06/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.06/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.06/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_full_bw                           [BwDemod]
% 15.06/2.50  --sup_immed_triv                        [TrivRules]
% 15.06/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.06/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_immed_bw_main                     []
% 15.06/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.06/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.06/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.06/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.06/2.50  
% 15.06/2.50  ------ Combination Options
% 15.06/2.50  
% 15.06/2.50  --comb_res_mult                         3
% 15.06/2.50  --comb_sup_mult                         2
% 15.06/2.50  --comb_inst_mult                        10
% 15.06/2.50  
% 15.06/2.50  ------ Debug Options
% 15.06/2.50  
% 15.06/2.50  --dbg_backtrace                         false
% 15.06/2.50  --dbg_dump_prop_clauses                 false
% 15.06/2.50  --dbg_dump_prop_clauses_file            -
% 15.06/2.50  --dbg_out_stat                          false
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  ------ Proving...
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  % SZS status Theorem for theBenchmark.p
% 15.06/2.50  
% 15.06/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.06/2.50  
% 15.06/2.50  fof(f1,axiom,(
% 15.06/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f26,plain,(
% 15.06/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.06/2.50    inference(ennf_transformation,[],[f1])).
% 15.06/2.50  
% 15.06/2.50  fof(f48,plain,(
% 15.06/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.06/2.50    inference(nnf_transformation,[],[f26])).
% 15.06/2.50  
% 15.06/2.50  fof(f49,plain,(
% 15.06/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.06/2.50    inference(rectify,[],[f48])).
% 15.06/2.50  
% 15.06/2.50  fof(f50,plain,(
% 15.06/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f51,plain,(
% 15.06/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.06/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 15.06/2.50  
% 15.06/2.50  fof(f76,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f51])).
% 15.06/2.50  
% 15.06/2.50  fof(f7,axiom,(
% 15.06/2.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f28,plain,(
% 15.06/2.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 15.06/2.50    inference(ennf_transformation,[],[f7])).
% 15.06/2.50  
% 15.06/2.50  fof(f85,plain,(
% 15.06/2.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f28])).
% 15.06/2.50  
% 15.06/2.50  fof(f13,axiom,(
% 15.06/2.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f36,plain,(
% 15.06/2.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f13])).
% 15.06/2.50  
% 15.06/2.50  fof(f95,plain,(
% 15.06/2.50    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f36])).
% 15.06/2.50  
% 15.06/2.50  fof(f20,conjecture,(
% 15.06/2.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f21,negated_conjecture,(
% 15.06/2.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 15.06/2.50    inference(negated_conjecture,[],[f20])).
% 15.06/2.50  
% 15.06/2.50  fof(f22,plain,(
% 15.06/2.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 15.06/2.50    inference(pure_predicate_removal,[],[f21])).
% 15.06/2.50  
% 15.06/2.50  fof(f23,plain,(
% 15.06/2.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 15.06/2.50    inference(pure_predicate_removal,[],[f22])).
% 15.06/2.50  
% 15.06/2.50  fof(f24,plain,(
% 15.06/2.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 15.06/2.50    inference(pure_predicate_removal,[],[f23])).
% 15.06/2.50  
% 15.06/2.50  fof(f46,plain,(
% 15.06/2.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 15.06/2.50    inference(ennf_transformation,[],[f24])).
% 15.06/2.50  
% 15.06/2.50  fof(f47,plain,(
% 15.06/2.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 15.06/2.50    inference(flattening,[],[f46])).
% 15.06/2.50  
% 15.06/2.50  fof(f70,plain,(
% 15.06/2.50    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 15.06/2.50    inference(nnf_transformation,[],[f47])).
% 15.06/2.50  
% 15.06/2.50  fof(f71,plain,(
% 15.06/2.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 15.06/2.50    inference(flattening,[],[f70])).
% 15.06/2.50  
% 15.06/2.50  fof(f73,plain,(
% 15.06/2.50    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK6) | ~v1_subset_1(sK6,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK6) | v1_subset_1(sK6,u1_struct_0(X0))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK6,X0) & ~v1_xboole_0(sK6))) )),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f72,plain,(
% 15.06/2.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK5),X1) | ~v1_subset_1(X1,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),X1) | v1_subset_1(X1,u1_struct_0(sK5))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(X1,sK5) & ~v1_xboole_0(X1)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5))),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f74,plain,(
% 15.06/2.50    ((r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(sK6,sK5) & ~v1_xboole_0(sK6)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5)),
% 15.06/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f71,f73,f72])).
% 15.06/2.50  
% 15.06/2.50  fof(f115,plain,(
% 15.06/2.50    l1_orders_2(sK5)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f118,plain,(
% 15.06/2.50    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f9,axiom,(
% 15.06/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f54,plain,(
% 15.06/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.06/2.50    inference(nnf_transformation,[],[f9])).
% 15.06/2.50  
% 15.06/2.50  fof(f87,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.06/2.50    inference(cnf_transformation,[],[f54])).
% 15.06/2.50  
% 15.06/2.50  fof(f15,axiom,(
% 15.06/2.50    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f39,plain,(
% 15.06/2.50    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f15])).
% 15.06/2.50  
% 15.06/2.50  fof(f101,plain,(
% 15.06/2.50    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f39])).
% 15.06/2.50  
% 15.06/2.50  fof(f19,axiom,(
% 15.06/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f45,plain,(
% 15.06/2.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.06/2.50    inference(ennf_transformation,[],[f19])).
% 15.06/2.50  
% 15.06/2.50  fof(f69,plain,(
% 15.06/2.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.06/2.50    inference(nnf_transformation,[],[f45])).
% 15.06/2.50  
% 15.06/2.50  fof(f111,plain,(
% 15.06/2.50    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.06/2.50    inference(cnf_transformation,[],[f69])).
% 15.06/2.50  
% 15.06/2.50  fof(f88,plain,(
% 15.06/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f54])).
% 15.06/2.50  
% 15.06/2.50  fof(f120,plain,(
% 15.06/2.50    r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f14,axiom,(
% 15.06/2.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f37,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f14])).
% 15.06/2.50  
% 15.06/2.50  fof(f38,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(flattening,[],[f37])).
% 15.06/2.50  
% 15.06/2.50  fof(f59,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(nnf_transformation,[],[f38])).
% 15.06/2.50  
% 15.06/2.50  fof(f60,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(flattening,[],[f59])).
% 15.06/2.50  
% 15.06/2.50  fof(f61,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(rectify,[],[f60])).
% 15.06/2.50  
% 15.06/2.50  fof(f62,plain,(
% 15.06/2.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f63,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).
% 15.06/2.50  
% 15.06/2.50  fof(f97,plain,(
% 15.06/2.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f63])).
% 15.06/2.50  
% 15.06/2.50  fof(f123,plain,(
% 15.06/2.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(equality_resolution,[],[f97])).
% 15.06/2.50  
% 15.06/2.50  fof(f17,axiom,(
% 15.06/2.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f25,plain,(
% 15.06/2.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 15.06/2.50    inference(pure_predicate_removal,[],[f17])).
% 15.06/2.50  
% 15.06/2.50  fof(f41,plain,(
% 15.06/2.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 15.06/2.50    inference(ennf_transformation,[],[f25])).
% 15.06/2.50  
% 15.06/2.50  fof(f42,plain,(
% 15.06/2.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 15.06/2.50    inference(flattening,[],[f41])).
% 15.06/2.50  
% 15.06/2.50  fof(f103,plain,(
% 15.06/2.50    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f42])).
% 15.06/2.50  
% 15.06/2.50  fof(f114,plain,(
% 15.06/2.50    v1_yellow_0(sK5)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f112,plain,(
% 15.06/2.50    ~v2_struct_0(sK5)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f113,plain,(
% 15.06/2.50    v5_orders_2(sK5)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f18,axiom,(
% 15.06/2.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f43,plain,(
% 15.06/2.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f18])).
% 15.06/2.50  
% 15.06/2.50  fof(f44,plain,(
% 15.06/2.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(flattening,[],[f43])).
% 15.06/2.50  
% 15.06/2.50  fof(f64,plain,(
% 15.06/2.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(nnf_transformation,[],[f44])).
% 15.06/2.50  
% 15.06/2.50  fof(f65,plain,(
% 15.06/2.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(rectify,[],[f64])).
% 15.06/2.50  
% 15.06/2.50  fof(f67,plain,(
% 15.06/2.50    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,X2,sK4(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))) )),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f66,plain,(
% 15.06/2.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK3(X0,X1),X3) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f68,plain,(
% 15.06/2.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f65,f67,f66])).
% 15.06/2.50  
% 15.06/2.50  fof(f104,plain,(
% 15.06/2.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f68])).
% 15.06/2.50  
% 15.06/2.50  fof(f10,axiom,(
% 15.06/2.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f31,plain,(
% 15.06/2.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 15.06/2.50    inference(ennf_transformation,[],[f10])).
% 15.06/2.50  
% 15.06/2.50  fof(f32,plain,(
% 15.06/2.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.06/2.50    inference(flattening,[],[f31])).
% 15.06/2.50  
% 15.06/2.50  fof(f89,plain,(
% 15.06/2.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f32])).
% 15.06/2.50  
% 15.06/2.50  fof(f117,plain,(
% 15.06/2.50    v13_waybel_0(sK6,sK5)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f6,axiom,(
% 15.06/2.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f84,plain,(
% 15.06/2.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.06/2.50    inference(cnf_transformation,[],[f6])).
% 15.06/2.50  
% 15.06/2.50  fof(f12,axiom,(
% 15.06/2.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f34,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f12])).
% 15.06/2.50  
% 15.06/2.50  fof(f35,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(flattening,[],[f34])).
% 15.06/2.50  
% 15.06/2.50  fof(f55,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(nnf_transformation,[],[f35])).
% 15.06/2.50  
% 15.06/2.50  fof(f56,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(rectify,[],[f55])).
% 15.06/2.50  
% 15.06/2.50  fof(f57,plain,(
% 15.06/2.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 15.06/2.50    introduced(choice_axiom,[])).
% 15.06/2.50  
% 15.06/2.50  fof(f58,plain,(
% 15.06/2.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 15.06/2.50  
% 15.06/2.50  fof(f93,plain,(
% 15.06/2.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f58])).
% 15.06/2.50  
% 15.06/2.50  fof(f11,axiom,(
% 15.06/2.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f33,plain,(
% 15.06/2.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 15.06/2.50    inference(ennf_transformation,[],[f11])).
% 15.06/2.50  
% 15.06/2.50  fof(f90,plain,(
% 15.06/2.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f33])).
% 15.06/2.50  
% 15.06/2.50  fof(f75,plain,(
% 15.06/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f51])).
% 15.06/2.50  
% 15.06/2.50  fof(f77,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f51])).
% 15.06/2.50  
% 15.06/2.50  fof(f110,plain,(
% 15.06/2.50    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.06/2.50    inference(cnf_transformation,[],[f69])).
% 15.06/2.50  
% 15.06/2.50  fof(f125,plain,(
% 15.06/2.50    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 15.06/2.50    inference(equality_resolution,[],[f110])).
% 15.06/2.50  
% 15.06/2.50  fof(f16,axiom,(
% 15.06/2.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f40,plain,(
% 15.06/2.50    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 15.06/2.50    inference(ennf_transformation,[],[f16])).
% 15.06/2.50  
% 15.06/2.50  fof(f102,plain,(
% 15.06/2.50    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f40])).
% 15.06/2.50  
% 15.06/2.50  fof(f2,axiom,(
% 15.06/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f52,plain,(
% 15.06/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.06/2.50    inference(nnf_transformation,[],[f2])).
% 15.06/2.50  
% 15.06/2.50  fof(f53,plain,(
% 15.06/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.06/2.50    inference(flattening,[],[f52])).
% 15.06/2.50  
% 15.06/2.50  fof(f78,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.06/2.50    inference(cnf_transformation,[],[f53])).
% 15.06/2.50  
% 15.06/2.50  fof(f122,plain,(
% 15.06/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.06/2.50    inference(equality_resolution,[],[f78])).
% 15.06/2.50  
% 15.06/2.50  fof(f119,plain,(
% 15.06/2.50    ~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f4,axiom,(
% 15.06/2.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f82,plain,(
% 15.06/2.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 15.06/2.50    inference(cnf_transformation,[],[f4])).
% 15.06/2.50  
% 15.06/2.50  fof(f3,axiom,(
% 15.06/2.50    ! [X0] : k2_subset_1(X0) = X0),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f81,plain,(
% 15.06/2.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.06/2.50    inference(cnf_transformation,[],[f3])).
% 15.06/2.50  
% 15.06/2.50  fof(f8,axiom,(
% 15.06/2.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.06/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.06/2.50  
% 15.06/2.50  fof(f29,plain,(
% 15.06/2.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.06/2.50    inference(ennf_transformation,[],[f8])).
% 15.06/2.50  
% 15.06/2.50  fof(f30,plain,(
% 15.06/2.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.06/2.50    inference(flattening,[],[f29])).
% 15.06/2.50  
% 15.06/2.50  fof(f86,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f30])).
% 15.06/2.50  
% 15.06/2.50  fof(f116,plain,(
% 15.06/2.50    ~v1_xboole_0(sK6)),
% 15.06/2.50    inference(cnf_transformation,[],[f74])).
% 15.06/2.50  
% 15.06/2.50  fof(f107,plain,(
% 15.06/2.50    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f68])).
% 15.06/2.50  
% 15.06/2.50  fof(f105,plain,(
% 15.06/2.50    ( ! [X0,X1] : (v13_waybel_0(X1,X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f68])).
% 15.06/2.50  
% 15.06/2.50  fof(f91,plain,(
% 15.06/2.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f58])).
% 15.06/2.50  
% 15.06/2.50  fof(f80,plain,(
% 15.06/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.06/2.50    inference(cnf_transformation,[],[f53])).
% 15.06/2.50  
% 15.06/2.50  fof(f79,plain,(
% 15.06/2.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.06/2.50    inference(cnf_transformation,[],[f53])).
% 15.06/2.50  
% 15.06/2.50  fof(f121,plain,(
% 15.06/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.06/2.50    inference(equality_resolution,[],[f79])).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1,plain,
% 15.06/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2912,plain,
% 15.06/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.06/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_10,plain,
% 15.06/2.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2906,plain,
% 15.06/2.50      ( m1_subset_1(X0,X1) = iProver_top
% 15.06/2.50      | r2_hidden(X0,X1) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4434,plain,
% 15.06/2.50      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 15.06/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2912,c_2906]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_20,plain,
% 15.06/2.50      ( ~ l1_orders_2(X0)
% 15.06/2.50      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_42,negated_conjecture,
% 15.06/2.50      ( l1_orders_2(sK5) ),
% 15.06/2.50      inference(cnf_transformation,[],[f115]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_843,plain,
% 15.06/2.50      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_844,plain,
% 15.06/2.50      ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_843]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_39,negated_conjecture,
% 15.06/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 15.06/2.50      inference(cnf_transformation,[],[f118]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2901,plain,
% 15.06/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_13,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2904,plain,
% 15.06/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.06/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4109,plain,
% 15.06/2.50      ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2901,c_2904]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_26,plain,
% 15.06/2.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f101]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_834,plain,
% 15.06/2.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_26,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_835,plain,
% 15.06/2.50      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_834]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2888,plain,
% 15.06/2.50      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_35,plain,
% 15.06/2.50      ( v1_subset_1(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.06/2.50      | X0 = X1 ),
% 15.06/2.50      inference(cnf_transformation,[],[f111]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_12,plain,
% 15.06/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_357,plain,
% 15.06/2.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.06/2.50      inference(prop_impl,[status(thm)],[c_12]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_358,plain,
% 15.06/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_357]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_446,plain,
% 15.06/2.50      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 15.06/2.50      inference(bin_hyper_res,[status(thm)],[c_35,c_358]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_37,negated_conjecture,
% 15.06/2.50      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 15.06/2.50      inference(cnf_transformation,[],[f120]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_361,plain,
% 15.06/2.50      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 15.06/2.50      inference(prop_impl,[status(thm)],[c_37]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_628,plain,
% 15.06/2.50      ( r2_hidden(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | ~ r1_tarski(X0,X1)
% 15.06/2.50      | X1 = X0
% 15.06/2.50      | u1_struct_0(sK5) != X1
% 15.06/2.50      | sK6 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_446,c_361]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_629,plain,
% 15.06/2.50      ( r2_hidden(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 15.06/2.50      | u1_struct_0(sK5) = sK6 ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_628]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2898,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 15.06/2.50      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_52,plain,
% 15.06/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_630,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 15.06/2.50      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3290,plain,
% 15.06/2.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | r1_tarski(sK6,u1_struct_0(sK5)) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3291,plain,
% 15.06/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_3290]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_5100,plain,
% 15.06/2.50      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top
% 15.06/2.50      | u1_struct_0(sK5) = sK6 ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_2898,c_52,c_630,c_3291]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_5101,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_5100]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_24,plain,
% 15.06/2.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.06/2.50      | ~ r2_lattice3(X0,X1,X2)
% 15.06/2.50      | ~ r1_yellow_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f123]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_270,plain,
% 15.06/2.50      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ r1_yellow_0(X0,X1)
% 15.06/2.50      | ~ r2_lattice3(X0,X1,X2)
% 15.06/2.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_24,c_26]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_271,plain,
% 15.06/2.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.06/2.50      | ~ r2_lattice3(X0,X1,X2)
% 15.06/2.50      | ~ r1_yellow_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_270]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_28,plain,
% 15.06/2.50      ( r1_yellow_0(X0,k1_xboole_0)
% 15.06/2.50      | v2_struct_0(X0)
% 15.06/2.50      | ~ v5_orders_2(X0)
% 15.06/2.50      | ~ v1_yellow_0(X0)
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f103]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_43,negated_conjecture,
% 15.06/2.50      ( v1_yellow_0(sK5) ),
% 15.06/2.50      inference(cnf_transformation,[],[f114]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_612,plain,
% 15.06/2.50      ( r1_yellow_0(X0,k1_xboole_0)
% 15.06/2.50      | v2_struct_0(X0)
% 15.06/2.50      | ~ v5_orders_2(X0)
% 15.06/2.50      | ~ l1_orders_2(X0)
% 15.06/2.50      | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_28,c_43]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_613,plain,
% 15.06/2.50      ( r1_yellow_0(sK5,k1_xboole_0)
% 15.06/2.50      | v2_struct_0(sK5)
% 15.06/2.50      | ~ v5_orders_2(sK5)
% 15.06/2.50      | ~ l1_orders_2(sK5) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_612]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_45,negated_conjecture,
% 15.06/2.50      ( ~ v2_struct_0(sK5) ),
% 15.06/2.50      inference(cnf_transformation,[],[f112]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_44,negated_conjecture,
% 15.06/2.50      ( v5_orders_2(sK5) ),
% 15.06/2.50      inference(cnf_transformation,[],[f113]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_78,plain,
% 15.06/2.50      ( r1_yellow_0(sK5,k1_xboole_0)
% 15.06/2.50      | v2_struct_0(sK5)
% 15.06/2.50      | ~ v5_orders_2(sK5)
% 15.06/2.50      | ~ v1_yellow_0(sK5)
% 15.06/2.50      | ~ l1_orders_2(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_28]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_615,plain,
% 15.06/2.50      ( r1_yellow_0(sK5,k1_xboole_0) ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_613,c_45,c_44,c_43,c_42,c_78]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_662,plain,
% 15.06/2.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 15.06/2.50      | ~ r2_lattice3(X0,X1,X2)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ l1_orders_2(X0)
% 15.06/2.50      | sK5 != X0
% 15.06/2.50      | k1_xboole_0 != X1 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_271,c_615]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_663,plain,
% 15.06/2.50      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 15.06/2.50      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 15.06/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 15.06/2.50      | ~ l1_orders_2(sK5) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_662]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_667,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 15.06/2.50      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 15.06/2.50      | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_663,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_668,plain,
% 15.06/2.50      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 15.06/2.50      | ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 15.06/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_667]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2896,plain,
% 15.06/2.50      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3030,plain,
% 15.06/2.50      ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(light_normalisation,[status(thm)],[c_2896,c_844]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_34,plain,
% 15.06/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.06/2.50      | ~ v13_waybel_0(X3,X0)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 15.06/2.50      | ~ r2_hidden(X1,X3)
% 15.06/2.50      | r2_hidden(X2,X3)
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f104]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_787,plain,
% 15.06/2.50      ( ~ r1_orders_2(X0,X1,X2)
% 15.06/2.50      | ~ v13_waybel_0(X3,X0)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 15.06/2.50      | ~ r2_hidden(X1,X3)
% 15.06/2.50      | r2_hidden(X2,X3)
% 15.06/2.50      | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_34,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_788,plain,
% 15.06/2.50      ( ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ v13_waybel_0(X2,sK5)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r2_hidden(X0,X2)
% 15.06/2.50      | r2_hidden(X1,X2) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_787]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_14,plain,
% 15.06/2.50      ( m1_subset_1(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.06/2.50      | ~ r2_hidden(X0,X2) ),
% 15.06/2.50      inference(cnf_transformation,[],[f89]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_804,plain,
% 15.06/2.50      ( ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ v13_waybel_0(X2,sK5)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r2_hidden(X0,X2)
% 15.06/2.50      | r2_hidden(X1,X2) ),
% 15.06/2.50      inference(forward_subsumption_resolution,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_788,c_14]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2891,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 15.06/2.50      | v13_waybel_0(X2,sK5) != iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.06/2.50      | r2_hidden(X1,X2) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4383,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 15.06/2.50      | v13_waybel_0(sK6,sK5) != iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.06/2.50      | r2_hidden(X1,sK6) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2901,c_2891]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_40,negated_conjecture,
% 15.06/2.50      ( v13_waybel_0(sK6,sK5) ),
% 15.06/2.50      inference(cnf_transformation,[],[f117]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1024,plain,
% 15.06/2.50      ( ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r2_hidden(X0,X2)
% 15.06/2.50      | r2_hidden(X1,X2)
% 15.06/2.50      | sK6 != X2
% 15.06/2.50      | sK5 != sK5 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_40,c_804]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1025,plain,
% 15.06/2.50      ( ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r2_hidden(X0,sK6)
% 15.06/2.50      | r2_hidden(X1,sK6) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_1024]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1027,plain,
% 15.06/2.50      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ r2_hidden(X0,sK6)
% 15.06/2.50      | r2_hidden(X1,sK6) ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_1025,c_39]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1028,plain,
% 15.06/2.50      ( ~ r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ r2_hidden(X0,sK6)
% 15.06/2.50      | r2_hidden(X1,sK6) ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_1027]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_1029,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.06/2.50      | r2_hidden(X1,sK6) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_1028]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4730,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) != iProver_top
% 15.06/2.50      | r2_hidden(X1,sK6) = iProver_top ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_4383,c_1029]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4739,plain,
% 15.06/2.50      ( r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) = iProver_top
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_3030,c_4730]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_5109,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_lattice3(sK5,k1_xboole_0,X0) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_5101,c_4739]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_9,plain,
% 15.06/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.06/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2907,plain,
% 15.06/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4107,plain,
% 15.06/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2907,c_2904]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_17,plain,
% 15.06/2.50      ( r2_lattice3(X0,X1,X2)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | r2_hidden(sK1(X0,X1,X2),X1)
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f93]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_884,plain,
% 15.06/2.50      ( r2_lattice3(X0,X1,X2)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | r2_hidden(sK1(X0,X1,X2),X1)
% 15.06/2.50      | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_17,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_885,plain,
% 15.06/2.50      ( r2_lattice3(sK5,X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | r2_hidden(sK1(sK5,X0,X1),X0) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_884]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2885,plain,
% 15.06/2.50      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(sK1(sK5,X0,X1),X0) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_15,plain,
% 15.06/2.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2902,plain,
% 15.06/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.06/2.50      | r1_tarski(X1,X0) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4049,plain,
% 15.06/2.50      ( r2_lattice3(sK5,X0,X1) = iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r1_tarski(X0,sK1(sK5,X0,X1)) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2885,c_2902]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_5246,plain,
% 15.06/2.50      ( r2_lattice3(sK5,k1_xboole_0,X0) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_4107,c_4049]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_15643,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) = iProver_top ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_5109,c_5246]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_15655,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),sK6) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2888,c_15643]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2,plain,
% 15.06/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.06/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2911,plain,
% 15.06/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.06/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.06/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_16549,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r1_tarski(sK6,X1) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_15655,c_2911]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_18010,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r1_tarski(X2,X1) != iProver_top
% 15.06/2.50      | r1_tarski(sK6,X2) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_16549,c_2911]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_23897,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
% 15.06/2.50      | r1_tarski(sK6,sK6) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_4109,c_18010]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3555,plain,
% 15.06/2.50      ( r2_hidden(sK0(X0,sK6),X0) | r1_tarski(X0,sK6) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6027,plain,
% 15.06/2.50      ( r2_hidden(sK0(sK6,sK6),sK6) | r1_tarski(sK6,sK6) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3555]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6029,plain,
% 15.06/2.50      ( r2_hidden(sK0(sK6,sK6),sK6) = iProver_top
% 15.06/2.50      | r1_tarski(sK6,sK6) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_6027]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_0,plain,
% 15.06/2.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3556,plain,
% 15.06/2.50      ( ~ r2_hidden(sK0(X0,sK6),sK6) | r1_tarski(X0,sK6) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6028,plain,
% 15.06/2.50      ( ~ r2_hidden(sK0(sK6,sK6),sK6) | r1_tarski(sK6,sK6) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3556]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6031,plain,
% 15.06/2.50      ( r2_hidden(sK0(sK6,sK6),sK6) != iProver_top
% 15.06/2.50      | r1_tarski(sK6,sK6) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_6028]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_24191,plain,
% 15.06/2.50      ( r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top
% 15.06/2.50      | u1_struct_0(sK5) = sK6 ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_23897,c_6029,c_6031]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_24192,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(renaming,[status(thm)],[c_24191]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_24200,plain,
% 15.06/2.50      ( u1_struct_0(sK5) = sK6
% 15.06/2.50      | r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_24192,c_2911]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_36,plain,
% 15.06/2.50      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 15.06/2.50      inference(cnf_transformation,[],[f125]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_56,plain,
% 15.06/2.50      ( ~ v1_subset_1(sK5,sK5) | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_36]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_59,plain,
% 15.06/2.50      ( v1_subset_1(sK5,sK5)
% 15.06/2.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5))
% 15.06/2.50      | sK5 = sK5 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_35]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_27,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f102]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_81,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 15.06/2.50      | ~ l1_orders_2(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_27]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_126,plain,
% 15.06/2.50      ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) | ~ r1_tarski(sK5,sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_12]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_5,plain,
% 15.06/2.50      ( r1_tarski(X0,X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f122]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_143,plain,
% 15.06/2.50      ( r1_tarski(sK5,sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_5]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2107,plain,
% 15.06/2.50      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 15.06/2.50      theory(equality) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2121,plain,
% 15.06/2.50      ( k3_yellow_0(sK5) = k3_yellow_0(sK5) | sK5 != sK5 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_2107]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_38,negated_conjecture,
% 15.06/2.50      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 15.06/2.50      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 15.06/2.50      inference(cnf_transformation,[],[f119]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_359,plain,
% 15.06/2.50      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 15.06/2.50      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 15.06/2.50      inference(prop_impl,[status(thm)],[c_38]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_641,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 15.06/2.50      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | u1_struct_0(sK5) != X0
% 15.06/2.50      | sK6 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_36,c_359]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_642,plain,
% 15.06/2.50      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | sK6 != u1_struct_0(sK5) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_641]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2897,plain,
% 15.06/2.50      ( sK6 != u1_struct_0(sK5)
% 15.06/2.50      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_7,plain,
% 15.06/2.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 15.06/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2908,plain,
% 15.06/2.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6,plain,
% 15.06/2.50      ( k2_subset_1(X0) = X0 ),
% 15.06/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2928,plain,
% 15.06/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.06/2.50      inference(light_normalisation,[status(thm)],[c_2908,c_6]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3021,plain,
% 15.06/2.50      ( u1_struct_0(sK5) != sK6
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 15.06/2.50      inference(forward_subsumption_resolution,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_2897,c_2928]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3132,plain,
% 15.06/2.50      ( ~ r2_hidden(k3_yellow_0(sK5),sK6) | u1_struct_0(sK5) != sK6 ),
% 15.06/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_3021]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2097,plain,( X0 = X0 ),theory(equality) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3367,plain,
% 15.06/2.50      ( sK6 = sK6 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_2097]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_11,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_41,negated_conjecture,
% 15.06/2.50      ( ~ v1_xboole_0(sK6) ),
% 15.06/2.50      inference(cnf_transformation,[],[f116]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_597,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK6 != X1 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_11,c_41]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_598,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,sK6) | r2_hidden(X0,sK6) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_597]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6385,plain,
% 15.06/2.50      ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_598]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2102,plain,
% 15.06/2.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.06/2.50      theory(equality) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3316,plain,
% 15.06/2.50      ( m1_subset_1(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 15.06/2.50      | X0 != k3_yellow_0(sK5)
% 15.06/2.50      | X1 != u1_struct_0(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_2102]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3600,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(X0),X1)
% 15.06/2.50      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 15.06/2.50      | X1 != u1_struct_0(sK5)
% 15.06/2.50      | k3_yellow_0(X0) != k3_yellow_0(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3316]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_10647,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(X0),sK6)
% 15.06/2.50      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 15.06/2.50      | k3_yellow_0(X0) != k3_yellow_0(sK5)
% 15.06/2.50      | sK6 != u1_struct_0(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3600]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_10651,plain,
% 15.06/2.50      ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 15.06/2.50      | m1_subset_1(k3_yellow_0(sK5),sK6)
% 15.06/2.50      | k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 15.06/2.50      | sK6 != u1_struct_0(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_10647]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2098,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3610,plain,
% 15.06/2.50      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_2098]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4937,plain,
% 15.06/2.50      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3610]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_25472,plain,
% 15.06/2.50      ( u1_struct_0(sK5) != sK6 | sK6 = u1_struct_0(sK5) | sK6 != sK6 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_4937]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_25487,plain,
% 15.06/2.50      ( r2_hidden(k1_yellow_0(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_24200,c_42,c_56,c_59,c_81,c_126,c_143,c_2121,c_3132,
% 15.06/2.50                 c_3367,c_6385,c_10651,c_25472]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_25498,plain,
% 15.06/2.50      ( m1_subset_1(k1_yellow_0(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),X1) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_25487,c_2906]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_31,plain,
% 15.06/2.50      ( v13_waybel_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.06/2.50      | r2_hidden(sK3(X1,X0),X0)
% 15.06/2.50      | ~ l1_orders_2(X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f107]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_944,plain,
% 15.06/2.50      ( v13_waybel_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.06/2.50      | r2_hidden(sK3(X1,X0),X0)
% 15.06/2.50      | sK5 != X1 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_31,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_945,plain,
% 15.06/2.50      ( v13_waybel_0(X0,sK5)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | r2_hidden(sK3(sK5,X0),X0) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_944]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2881,plain,
% 15.06/2.50      ( v13_waybel_0(X0,sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,X0),X0) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_25627,plain,
% 15.06/2.50      ( v13_waybel_0(k1_yellow_0(sK5,X0),sK5) = iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,k1_yellow_0(sK5,X0)),k1_yellow_0(sK5,X0)) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_25498,c_2881]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_27093,plain,
% 15.06/2.50      ( v13_waybel_0(k1_yellow_0(sK5,k1_xboole_0),sK5) = iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_844,c_25627]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_27143,plain,
% 15.06/2.50      ( v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),k3_yellow_0(sK5)) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(light_normalisation,[status(thm)],[c_27093,c_844]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_33,plain,
% 15.06/2.50      ( v13_waybel_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.06/2.50      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 15.06/2.50      | ~ l1_orders_2(X1) ),
% 15.06/2.50      inference(cnf_transformation,[],[f105]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_914,plain,
% 15.06/2.50      ( v13_waybel_0(X0,X1)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.06/2.50      | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
% 15.06/2.50      | sK5 != X1 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_33,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_915,plain,
% 15.06/2.50      ( v13_waybel_0(X0,sK5)
% 15.06/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_914]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2883,plain,
% 15.06/2.50      ( v13_waybel_0(X0,sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | m1_subset_1(sK3(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_19,plain,
% 15.06/2.50      ( r1_orders_2(X0,X1,X2)
% 15.06/2.50      | ~ r2_lattice3(X0,X3,X2)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.06/2.50      | ~ r2_hidden(X1,X3)
% 15.06/2.50      | ~ l1_orders_2(X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f91]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_848,plain,
% 15.06/2.50      ( r1_orders_2(X0,X1,X2)
% 15.06/2.50      | ~ r2_lattice3(X0,X3,X2)
% 15.06/2.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 15.06/2.50      | ~ r2_hidden(X1,X3)
% 15.06/2.50      | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_19,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_849,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1)
% 15.06/2.50      | ~ r2_lattice3(sK5,X2,X1)
% 15.06/2.50      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 15.06/2.50      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 15.06/2.50      | ~ r2_hidden(X0,X2) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_848]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2887,plain,
% 15.06/2.50      ( r1_orders_2(sK5,X0,X1) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,X2,X1) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,X2) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3841,plain,
% 15.06/2.50      ( r1_orders_2(sK5,sK3(sK5,X0),X1) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,X2,X1) != iProver_top
% 15.06/2.50      | v13_waybel_0(X0,sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,X0),X2) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2883,c_2887]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_27171,plain,
% 15.06/2.50      ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 15.06/2.50      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | m1_subset_1(k3_yellow_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_27143,c_3841]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_25605,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),X0) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_844,c_25498]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_29069,plain,
% 15.06/2.50      ( r1_orders_2(sK5,sK3(sK5,k3_yellow_0(sK5)),X0) = iProver_top
% 15.06/2.50      | r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 15.06/2.50      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(forward_subsumption_resolution,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_27171,c_25605]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_29077,plain,
% 15.06/2.50      ( r2_lattice3(sK5,k3_yellow_0(sK5),X0) != iProver_top
% 15.06/2.50      | v13_waybel_0(k3_yellow_0(sK5),sK5) = iProver_top
% 15.06/2.50      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) = iProver_top
% 15.06/2.50      | r2_hidden(sK3(sK5,k3_yellow_0(sK5)),sK6) != iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_29069,c_4730]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_49,plain,
% 15.06/2.50      ( l1_orders_2(sK5) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_80,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
% 15.06/2.50      | l1_orders_2(X0) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_82,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top
% 15.06/2.50      | l1_orders_2(sK5) != iProver_top ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_80]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_6386,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_6385]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_10650,plain,
% 15.06/2.50      ( k3_yellow_0(X0) != k3_yellow_0(sK5)
% 15.06/2.50      | sK6 != u1_struct_0(sK5)
% 15.06/2.50      | m1_subset_1(k3_yellow_0(X0),sK6) = iProver_top
% 15.06/2.50      | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_10647]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_10652,plain,
% 15.06/2.50      ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 15.06/2.50      | sK6 != u1_struct_0(sK5)
% 15.06/2.50      | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_10650]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_30633,plain,
% 15.06/2.50      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 15.06/2.50      | r2_hidden(X0,sK6) = iProver_top ),
% 15.06/2.50      inference(global_propositional_subsumption,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_29077,c_42,c_56,c_59,c_81,c_126,c_143,c_2121,c_3132,
% 15.06/2.50                 c_3367,c_6385,c_10651,c_15643,c_25472]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_30650,plain,
% 15.06/2.50      ( r2_hidden(sK0(u1_struct_0(sK5),X0),sK6) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_4434,c_30633]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2913,plain,
% 15.06/2.50      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.06/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_65331,plain,
% 15.06/2.50      ( r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_30650,c_2913]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_827,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | sK5 != X0 ),
% 15.06/2.50      inference(resolution_lifted,[status(thm)],[c_27,c_42]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_828,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) ),
% 15.06/2.50      inference(unflattening,[status(thm)],[c_827]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_2889,plain,
% 15.06/2.50      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_30641,plain,
% 15.06/2.50      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 15.06/2.50      inference(superposition,[status(thm)],[c_2889,c_30633]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3,plain,
% 15.06/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.06/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3604,plain,
% 15.06/2.50      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4603,plain,
% 15.06/2.50      ( ~ r1_tarski(u1_struct_0(sK5),sK6)
% 15.06/2.50      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 15.06/2.50      | sK6 = u1_struct_0(sK5) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3604]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4604,plain,
% 15.06/2.50      ( sK6 = u1_struct_0(sK5)
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
% 15.06/2.50      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_4603]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_4,plain,
% 15.06/2.50      ( r1_tarski(X0,X0) ),
% 15.06/2.50      inference(cnf_transformation,[],[f121]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3524,plain,
% 15.06/2.50      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3527,plain,
% 15.06/2.50      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_3524]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3285,plain,
% 15.06/2.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_12]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3523,plain,
% 15.06/2.50      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 15.06/2.50      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 15.06/2.50      inference(instantiation,[status(thm)],[c_3285]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_3525,plain,
% 15.06/2.50      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 15.06/2.50      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_3523]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(c_643,plain,
% 15.06/2.50      ( sK6 != u1_struct_0(sK5)
% 15.06/2.50      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 15.06/2.50      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 15.06/2.50      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 15.06/2.50  
% 15.06/2.50  cnf(contradiction,plain,
% 15.06/2.50      ( $false ),
% 15.06/2.50      inference(minisat,
% 15.06/2.50                [status(thm)],
% 15.06/2.50                [c_65331,c_30641,c_4604,c_3527,c_3525,c_3291,c_643,c_52]) ).
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.06/2.50  
% 15.06/2.50  ------                               Statistics
% 15.06/2.50  
% 15.06/2.50  ------ General
% 15.06/2.50  
% 15.06/2.50  abstr_ref_over_cycles:                  0
% 15.06/2.50  abstr_ref_under_cycles:                 0
% 15.06/2.50  gc_basic_clause_elim:                   0
% 15.06/2.50  forced_gc_time:                         0
% 15.06/2.50  parsing_time:                           0.014
% 15.06/2.50  unif_index_cands_time:                  0.
% 15.06/2.50  unif_index_add_time:                    0.
% 15.06/2.50  orderings_time:                         0.
% 15.06/2.50  out_proof_time:                         0.018
% 15.06/2.50  total_time:                             1.561
% 15.06/2.50  num_of_symbols:                         57
% 15.06/2.50  num_of_terms:                           34227
% 15.06/2.50  
% 15.06/2.50  ------ Preprocessing
% 15.06/2.50  
% 15.06/2.50  num_of_splits:                          0
% 15.06/2.50  num_of_split_atoms:                     0
% 15.06/2.50  num_of_reused_defs:                     0
% 15.06/2.50  num_eq_ax_congr_red:                    36
% 15.06/2.50  num_of_sem_filtered_clauses:            1
% 15.06/2.50  num_of_subtypes:                        0
% 15.06/2.50  monotx_restored_types:                  0
% 15.06/2.50  sat_num_of_epr_types:                   0
% 15.06/2.50  sat_num_of_non_cyclic_types:            0
% 15.06/2.50  sat_guarded_non_collapsed_types:        0
% 15.06/2.50  num_pure_diseq_elim:                    0
% 15.06/2.50  simp_replaced_by:                       0
% 15.06/2.50  res_preprocessed:                       185
% 15.06/2.50  prep_upred:                             0
% 15.06/2.50  prep_unflattend:                        68
% 15.06/2.50  smt_new_axioms:                         0
% 15.06/2.50  pred_elim_cands:                        6
% 15.06/2.50  pred_elim:                              7
% 15.06/2.50  pred_elim_cl:                           8
% 15.06/2.50  pred_elim_cycles:                       11
% 15.06/2.50  merged_defs:                            10
% 15.06/2.50  merged_defs_ncl:                        0
% 15.06/2.50  bin_hyper_res:                          12
% 15.06/2.50  prep_cycles:                            4
% 15.06/2.50  pred_elim_time:                         0.023
% 15.06/2.50  splitting_time:                         0.
% 15.06/2.50  sem_filter_time:                        0.
% 15.06/2.50  monotx_time:                            0.001
% 15.06/2.50  subtype_inf_time:                       0.
% 15.06/2.50  
% 15.06/2.50  ------ Problem properties
% 15.06/2.50  
% 15.06/2.50  clauses:                                36
% 15.06/2.50  conjectures:                            2
% 15.06/2.50  epr:                                    7
% 15.06/2.50  horn:                                   26
% 15.06/2.50  ground:                                 7
% 15.06/2.50  unary:                                  10
% 15.06/2.50  binary:                                 7
% 15.06/2.50  lits:                                   89
% 15.06/2.50  lits_eq:                                8
% 15.06/2.50  fd_pure:                                0
% 15.06/2.50  fd_pseudo:                              0
% 15.06/2.50  fd_cond:                                3
% 15.06/2.50  fd_pseudo_cond:                         1
% 15.06/2.50  ac_symbols:                             0
% 15.06/2.50  
% 15.06/2.50  ------ Propositional Solver
% 15.06/2.50  
% 15.06/2.50  prop_solver_calls:                      31
% 15.06/2.50  prop_fast_solver_calls:                 3602
% 15.06/2.50  smt_solver_calls:                       0
% 15.06/2.50  smt_fast_solver_calls:                  0
% 15.06/2.50  prop_num_of_clauses:                    19820
% 15.06/2.50  prop_preprocess_simplified:             35223
% 15.06/2.50  prop_fo_subsumed:                       206
% 15.06/2.50  prop_solver_time:                       0.
% 15.06/2.50  smt_solver_time:                        0.
% 15.06/2.50  smt_fast_solver_time:                   0.
% 15.06/2.50  prop_fast_solver_time:                  0.
% 15.06/2.50  prop_unsat_core_time:                   0.001
% 15.06/2.50  
% 15.06/2.50  ------ QBF
% 15.06/2.50  
% 15.06/2.50  qbf_q_res:                              0
% 15.06/2.50  qbf_num_tautologies:                    0
% 15.06/2.50  qbf_prep_cycles:                        0
% 15.06/2.50  
% 15.06/2.50  ------ BMC1
% 15.06/2.50  
% 15.06/2.50  bmc1_current_bound:                     -1
% 15.06/2.50  bmc1_last_solved_bound:                 -1
% 15.06/2.50  bmc1_unsat_core_size:                   -1
% 15.06/2.50  bmc1_unsat_core_parents_size:           -1
% 15.06/2.50  bmc1_merge_next_fun:                    0
% 15.06/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.06/2.50  
% 15.06/2.50  ------ Instantiation
% 15.06/2.50  
% 15.06/2.50  inst_num_of_clauses:                    4425
% 15.06/2.50  inst_num_in_passive:                    1797
% 15.06/2.50  inst_num_in_active:                     1797
% 15.06/2.50  inst_num_in_unprocessed:                833
% 15.06/2.50  inst_num_of_loops:                      2340
% 15.06/2.50  inst_num_of_learning_restarts:          0
% 15.06/2.50  inst_num_moves_active_passive:          540
% 15.06/2.50  inst_lit_activity:                      0
% 15.06/2.50  inst_lit_activity_moves:                0
% 15.06/2.50  inst_num_tautologies:                   0
% 15.06/2.50  inst_num_prop_implied:                  0
% 15.06/2.50  inst_num_existing_simplified:           0
% 15.06/2.50  inst_num_eq_res_simplified:             0
% 15.06/2.50  inst_num_child_elim:                    0
% 15.06/2.50  inst_num_of_dismatching_blockings:      4559
% 15.06/2.50  inst_num_of_non_proper_insts:           5269
% 15.06/2.50  inst_num_of_duplicates:                 0
% 15.06/2.50  inst_inst_num_from_inst_to_res:         0
% 15.06/2.50  inst_dismatching_checking_time:         0.
% 15.06/2.50  
% 15.06/2.50  ------ Resolution
% 15.06/2.50  
% 15.06/2.50  res_num_of_clauses:                     0
% 15.06/2.50  res_num_in_passive:                     0
% 15.06/2.50  res_num_in_active:                      0
% 15.06/2.50  res_num_of_loops:                       189
% 15.06/2.50  res_forward_subset_subsumed:            351
% 15.06/2.50  res_backward_subset_subsumed:           4
% 15.06/2.50  res_forward_subsumed:                   0
% 15.06/2.50  res_backward_subsumed:                  0
% 15.06/2.50  res_forward_subsumption_resolution:     6
% 15.06/2.50  res_backward_subsumption_resolution:    0
% 15.06/2.50  res_clause_to_clause_subsumption:       15523
% 15.06/2.50  res_orphan_elimination:                 0
% 15.06/2.50  res_tautology_del:                      309
% 15.06/2.50  res_num_eq_res_simplified:              0
% 15.06/2.50  res_num_sel_changes:                    0
% 15.06/2.50  res_moves_from_active_to_pass:          0
% 15.06/2.50  
% 15.06/2.50  ------ Superposition
% 15.06/2.50  
% 15.06/2.50  sup_time_total:                         0.
% 15.06/2.50  sup_time_generating:                    0.
% 15.06/2.50  sup_time_sim_full:                      0.
% 15.06/2.50  sup_time_sim_immed:                     0.
% 15.06/2.50  
% 15.06/2.50  sup_num_of_clauses:                     1481
% 15.06/2.50  sup_num_in_active:                      447
% 15.06/2.50  sup_num_in_passive:                     1034
% 15.06/2.50  sup_num_of_loops:                       466
% 15.06/2.50  sup_fw_superposition:                   1129
% 15.06/2.50  sup_bw_superposition:                   1527
% 15.06/2.50  sup_immediate_simplified:               834
% 15.06/2.50  sup_given_eliminated:                   0
% 15.06/2.50  comparisons_done:                       0
% 15.06/2.50  comparisons_avoided:                    10
% 15.06/2.50  
% 15.06/2.50  ------ Simplifications
% 15.06/2.50  
% 15.06/2.50  
% 15.06/2.50  sim_fw_subset_subsumed:                 456
% 15.06/2.50  sim_bw_subset_subsumed:                 68
% 15.06/2.50  sim_fw_subsumed:                        244
% 15.06/2.50  sim_bw_subsumed:                        92
% 15.06/2.50  sim_fw_subsumption_res:                 11
% 15.06/2.50  sim_bw_subsumption_res:                 12
% 15.06/2.50  sim_tautology_del:                      31
% 15.06/2.50  sim_eq_tautology_del:                   10
% 15.06/2.50  sim_eq_res_simp:                        0
% 15.06/2.50  sim_fw_demodulated:                     4
% 15.06/2.50  sim_bw_demodulated:                     0
% 15.06/2.50  sim_light_normalised:                   31
% 15.06/2.50  sim_joinable_taut:                      0
% 15.06/2.50  sim_joinable_simp:                      0
% 15.06/2.50  sim_ac_normalised:                      0
% 15.06/2.50  sim_smt_subsumption:                    0
% 15.06/2.50  
%------------------------------------------------------------------------------
