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
% DateTime   : Thu Dec  3 12:28:24 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  266 (2138 expanded)
%              Number of clauses        :  158 ( 501 expanded)
%              Number of leaves         :   28 ( 407 expanded)
%              Depth                    :   34
%              Number of atoms          : 1042 (16590 expanded)
%              Number of equality atoms :  232 ( 615 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f96,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f42])).

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
    inference(flattening,[],[f69])).

fof(f72,plain,(
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

fof(f71,plain,
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

fof(f73,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f70,f72,f71])).

fof(f115,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f73])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f120,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f73])).

fof(f118,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f73])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f123,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f103,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f73])).

fof(f112,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f73])).

fof(f113,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f73])).

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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f39])).

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
    inference(rectify,[],[f63])).

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).

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
    inference(cnf_transformation,[],[f67])).

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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f73])).

fof(f116,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f73])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f119,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f73])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2744,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_1])).

cnf(c_292,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_2730,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_7604,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2744,c_2730])).

cnf(c_22,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_43,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_857,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_43])).

cnf(c_858,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_857])).

cnf(c_28,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_848,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_43])).

cnf(c_849,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_2718,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_19,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_898,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_43])).

cnf(c_899,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(c_2715,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_2746,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4041,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_2746])).

cnf(c_4222,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X1)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_4041])).

cnf(c_36,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_38,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_366,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_38])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_366])).

cnf(c_644,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_646,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_40])).

cnf(c_2727,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_26,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_28])).

cnf(c_272,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_271])).

cnf(c_29,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_44,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_605,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_44])).

cnf(c_606,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_45,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_79,plain,
    ( r1_yellow_0(sK6,k1_xboole_0)
    | v2_struct_0(sK6)
    | ~ v5_orders_2(sK6)
    | ~ v1_yellow_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_608,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_46,c_45,c_44,c_43,c_79])).

cnf(c_707,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_608])).

cnf(c_708,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_43])).

cnf(c_713,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_2724,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2752,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2724,c_858])).

cnf(c_2733,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_35,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_808,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_43])).

cnf(c_809,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_825,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_809,c_16])).

cnf(c_2720,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_4459,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_2720])).

cnf(c_53,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_41,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1036,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_825])).

cnf(c_1037,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_1038,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_4752,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4459,c_53,c_1038])).

cnf(c_4757,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2752,c_4752])).

cnf(c_6100,plain,
    ( u1_struct_0(sK6) = sK7
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_4757])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_51,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_52,plain,
    ( v13_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_136,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_140,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2084,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_2099,plain,
    ( k3_yellow_0(sK6) = k3_yellow_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2821,plain,
    ( r2_hidden(sK0(sK7),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2822,plain,
    ( r2_hidden(sK0(sK7),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2821])).

cnf(c_2953,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_3050,plain,
    ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),X0)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_3051,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3050])).

cnf(c_3005,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3345,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3062,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3611,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(instantiation,[status(thm)],[c_3062])).

cnf(c_3871,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK0(sK7),u1_struct_0(sK6))
    | ~ r2_hidden(sK0(sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_3611])).

cnf(c_3872,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(sK7),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK0(sK7),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3871])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_4098,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3130,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_2718])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2737,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4539,plain,
    ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_2737])).

cnf(c_3495,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK6))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4801,plain,
    ( ~ r2_hidden(sK0(sK7),u1_struct_0(sK6))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3495])).

cnf(c_4805,plain,
    ( r2_hidden(sK0(sK7),u1_struct_0(sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4801])).

cnf(c_2074,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3004,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_3360,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_6617,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_2076,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4823,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_6509,plain,
    ( r2_hidden(k3_yellow_0(sK6),X0)
    | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4823])).

cnf(c_12390,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_6509])).

cnf(c_12391,plain,
    ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12390])).

cnf(c_15908,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6100,c_51,c_52,c_53,c_136,c_140,c_2099,c_2752,c_2822,c_3051,c_3345,c_3872,c_4098,c_4539,c_4805,c_6617,c_12391])).

cnf(c_15919,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4222,c_15908])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_142,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_850,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_21476,plain,
    ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15919,c_142,c_850])).

cnf(c_21,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_862,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_43])).

cnf(c_863,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_2717,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_3683,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_2717])).

cnf(c_21485,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
    | r2_lattice3(sK6,sK7,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21476,c_3683])).

cnf(c_21493,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,sK7,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_21485])).

cnf(c_3276,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_3277,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3276])).

cnf(c_20559,plain,
    ( ~ r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_20560,plain,
    ( r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20559])).

cnf(c_22177,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21493,c_142,c_2752,c_3277,c_20560])).

cnf(c_22184,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_22177,c_4752])).

cnf(c_27,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_264,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_28])).

cnf(c_265,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_264])).

cnf(c_728,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | sK6 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_265,c_608])).

cnf(c_729,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_731,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_43])).

cnf(c_2723,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2748,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2723,c_858])).

cnf(c_15918,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2748,c_15908])).

cnf(c_22437,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22184,c_3130,c_15918])).

cnf(c_22438,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_22437])).

cnf(c_22452,plain,
    ( r1_tarski(u1_struct_0(sK6),X0) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_7604,c_22438])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2745,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_25530,plain,
    ( r1_tarski(u1_struct_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_22452,c_2745])).

cnf(c_2736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5661,plain,
    ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_2736])).

cnf(c_5738,plain,
    ( r1_tarski(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK6)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5661,c_2745])).

cnf(c_5747,plain,
    ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2744,c_5738])).

cnf(c_2741,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6449,plain,
    ( u1_struct_0(sK6) = sK7
    | r1_tarski(u1_struct_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5747,c_2741])).

cnf(c_15,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_364,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_39])).

cnf(c_631,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | k2_subset_1(X0) != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_364])).

cnf(c_632,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | k2_subset_1(u1_struct_0(sK6)) != sK7 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_2728,plain,
    ( k2_subset_1(u1_struct_0(sK6)) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_13,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2751,plain,
    ( u1_struct_0(sK6) != sK7
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2728,c_13])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3036,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4818,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),sK7)
    | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_4819,plain,
    ( r1_tarski(u1_struct_0(sK6),sK7) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4818])).

cnf(c_7731,plain,
    ( r1_tarski(u1_struct_0(sK6),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6449,c_51,c_53,c_2751,c_2822,c_3872,c_4539,c_4805,c_4819])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25530,c_7731])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.84/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.50  
% 7.84/1.50  ------  iProver source info
% 7.84/1.50  
% 7.84/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.50  git: non_committed_changes: false
% 7.84/1.50  git: last_make_outside_of_git: false
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  
% 7.84/1.50  ------ Input Options
% 7.84/1.50  
% 7.84/1.50  --out_options                           all
% 7.84/1.50  --tptp_safe_out                         true
% 7.84/1.50  --problem_path                          ""
% 7.84/1.50  --include_path                          ""
% 7.84/1.50  --clausifier                            res/vclausify_rel
% 7.84/1.50  --clausifier_options                    ""
% 7.84/1.50  --stdin                                 false
% 7.84/1.50  --stats_out                             all
% 7.84/1.50  
% 7.84/1.50  ------ General Options
% 7.84/1.50  
% 7.84/1.50  --fof                                   false
% 7.84/1.50  --time_out_real                         305.
% 7.84/1.50  --time_out_virtual                      -1.
% 7.84/1.50  --symbol_type_check                     false
% 7.84/1.50  --clausify_out                          false
% 7.84/1.50  --sig_cnt_out                           false
% 7.84/1.50  --trig_cnt_out                          false
% 7.84/1.50  --trig_cnt_out_tolerance                1.
% 7.84/1.50  --trig_cnt_out_sk_spl                   false
% 7.84/1.50  --abstr_cl_out                          false
% 7.84/1.50  
% 7.84/1.50  ------ Global Options
% 7.84/1.50  
% 7.84/1.50  --schedule                              default
% 7.84/1.50  --add_important_lit                     false
% 7.84/1.50  --prop_solver_per_cl                    1000
% 7.84/1.50  --min_unsat_core                        false
% 7.84/1.50  --soft_assumptions                      false
% 7.84/1.50  --soft_lemma_size                       3
% 7.84/1.50  --prop_impl_unit_size                   0
% 7.84/1.50  --prop_impl_unit                        []
% 7.84/1.50  --share_sel_clauses                     true
% 7.84/1.50  --reset_solvers                         false
% 7.84/1.50  --bc_imp_inh                            [conj_cone]
% 7.84/1.50  --conj_cone_tolerance                   3.
% 7.84/1.50  --extra_neg_conj                        none
% 7.84/1.50  --large_theory_mode                     true
% 7.84/1.50  --prolific_symb_bound                   200
% 7.84/1.50  --lt_threshold                          2000
% 7.84/1.50  --clause_weak_htbl                      true
% 7.84/1.50  --gc_record_bc_elim                     false
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing Options
% 7.84/1.50  
% 7.84/1.50  --preprocessing_flag                    true
% 7.84/1.50  --time_out_prep_mult                    0.1
% 7.84/1.50  --splitting_mode                        input
% 7.84/1.50  --splitting_grd                         true
% 7.84/1.50  --splitting_cvd                         false
% 7.84/1.50  --splitting_cvd_svl                     false
% 7.84/1.50  --splitting_nvd                         32
% 7.84/1.50  --sub_typing                            true
% 7.84/1.50  --prep_gs_sim                           true
% 7.84/1.50  --prep_unflatten                        true
% 7.84/1.50  --prep_res_sim                          true
% 7.84/1.50  --prep_upred                            true
% 7.84/1.50  --prep_sem_filter                       exhaustive
% 7.84/1.50  --prep_sem_filter_out                   false
% 7.84/1.50  --pred_elim                             true
% 7.84/1.50  --res_sim_input                         true
% 7.84/1.50  --eq_ax_congr_red                       true
% 7.84/1.50  --pure_diseq_elim                       true
% 7.84/1.50  --brand_transform                       false
% 7.84/1.50  --non_eq_to_eq                          false
% 7.84/1.50  --prep_def_merge                        true
% 7.84/1.50  --prep_def_merge_prop_impl              false
% 7.84/1.50  --prep_def_merge_mbd                    true
% 7.84/1.50  --prep_def_merge_tr_red                 false
% 7.84/1.50  --prep_def_merge_tr_cl                  false
% 7.84/1.50  --smt_preprocessing                     true
% 7.84/1.50  --smt_ac_axioms                         fast
% 7.84/1.50  --preprocessed_out                      false
% 7.84/1.50  --preprocessed_stats                    false
% 7.84/1.50  
% 7.84/1.50  ------ Abstraction refinement Options
% 7.84/1.50  
% 7.84/1.50  --abstr_ref                             []
% 7.84/1.50  --abstr_ref_prep                        false
% 7.84/1.50  --abstr_ref_until_sat                   false
% 7.84/1.50  --abstr_ref_sig_restrict                funpre
% 7.84/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.50  --abstr_ref_under                       []
% 7.84/1.50  
% 7.84/1.50  ------ SAT Options
% 7.84/1.50  
% 7.84/1.50  --sat_mode                              false
% 7.84/1.50  --sat_fm_restart_options                ""
% 7.84/1.50  --sat_gr_def                            false
% 7.84/1.50  --sat_epr_types                         true
% 7.84/1.50  --sat_non_cyclic_types                  false
% 7.84/1.50  --sat_finite_models                     false
% 7.84/1.50  --sat_fm_lemmas                         false
% 7.84/1.50  --sat_fm_prep                           false
% 7.84/1.50  --sat_fm_uc_incr                        true
% 7.84/1.50  --sat_out_model                         small
% 7.84/1.50  --sat_out_clauses                       false
% 7.84/1.50  
% 7.84/1.50  ------ QBF Options
% 7.84/1.50  
% 7.84/1.50  --qbf_mode                              false
% 7.84/1.50  --qbf_elim_univ                         false
% 7.84/1.50  --qbf_dom_inst                          none
% 7.84/1.50  --qbf_dom_pre_inst                      false
% 7.84/1.50  --qbf_sk_in                             false
% 7.84/1.50  --qbf_pred_elim                         true
% 7.84/1.50  --qbf_split                             512
% 7.84/1.50  
% 7.84/1.50  ------ BMC1 Options
% 7.84/1.50  
% 7.84/1.50  --bmc1_incremental                      false
% 7.84/1.50  --bmc1_axioms                           reachable_all
% 7.84/1.50  --bmc1_min_bound                        0
% 7.84/1.50  --bmc1_max_bound                        -1
% 7.84/1.50  --bmc1_max_bound_default                -1
% 7.84/1.50  --bmc1_symbol_reachability              true
% 7.84/1.50  --bmc1_property_lemmas                  false
% 7.84/1.50  --bmc1_k_induction                      false
% 7.84/1.50  --bmc1_non_equiv_states                 false
% 7.84/1.50  --bmc1_deadlock                         false
% 7.84/1.50  --bmc1_ucm                              false
% 7.84/1.50  --bmc1_add_unsat_core                   none
% 7.84/1.50  --bmc1_unsat_core_children              false
% 7.84/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.50  --bmc1_out_stat                         full
% 7.84/1.50  --bmc1_ground_init                      false
% 7.84/1.50  --bmc1_pre_inst_next_state              false
% 7.84/1.50  --bmc1_pre_inst_state                   false
% 7.84/1.50  --bmc1_pre_inst_reach_state             false
% 7.84/1.50  --bmc1_out_unsat_core                   false
% 7.84/1.50  --bmc1_aig_witness_out                  false
% 7.84/1.50  --bmc1_verbose                          false
% 7.84/1.50  --bmc1_dump_clauses_tptp                false
% 7.84/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.50  --bmc1_dump_file                        -
% 7.84/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.50  --bmc1_ucm_extend_mode                  1
% 7.84/1.50  --bmc1_ucm_init_mode                    2
% 7.84/1.50  --bmc1_ucm_cone_mode                    none
% 7.84/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.50  --bmc1_ucm_relax_model                  4
% 7.84/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.50  --bmc1_ucm_layered_model                none
% 7.84/1.50  --bmc1_ucm_max_lemma_size               10
% 7.84/1.50  
% 7.84/1.50  ------ AIG Options
% 7.84/1.50  
% 7.84/1.50  --aig_mode                              false
% 7.84/1.50  
% 7.84/1.50  ------ Instantiation Options
% 7.84/1.50  
% 7.84/1.50  --instantiation_flag                    true
% 7.84/1.50  --inst_sos_flag                         true
% 7.84/1.50  --inst_sos_phase                        true
% 7.84/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel_side                     num_symb
% 7.84/1.50  --inst_solver_per_active                1400
% 7.84/1.50  --inst_solver_calls_frac                1.
% 7.84/1.50  --inst_passive_queue_type               priority_queues
% 7.84/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.50  --inst_passive_queues_freq              [25;2]
% 7.84/1.50  --inst_dismatching                      true
% 7.84/1.50  --inst_eager_unprocessed_to_passive     true
% 7.84/1.50  --inst_prop_sim_given                   true
% 7.84/1.50  --inst_prop_sim_new                     false
% 7.84/1.50  --inst_subs_new                         false
% 7.84/1.50  --inst_eq_res_simp                      false
% 7.84/1.50  --inst_subs_given                       false
% 7.84/1.50  --inst_orphan_elimination               true
% 7.84/1.50  --inst_learning_loop_flag               true
% 7.84/1.50  --inst_learning_start                   3000
% 7.84/1.50  --inst_learning_factor                  2
% 7.84/1.50  --inst_start_prop_sim_after_learn       3
% 7.84/1.50  --inst_sel_renew                        solver
% 7.84/1.50  --inst_lit_activity_flag                true
% 7.84/1.50  --inst_restr_to_given                   false
% 7.84/1.50  --inst_activity_threshold               500
% 7.84/1.50  --inst_out_proof                        true
% 7.84/1.50  
% 7.84/1.50  ------ Resolution Options
% 7.84/1.50  
% 7.84/1.50  --resolution_flag                       true
% 7.84/1.50  --res_lit_sel                           adaptive
% 7.84/1.50  --res_lit_sel_side                      none
% 7.84/1.50  --res_ordering                          kbo
% 7.84/1.50  --res_to_prop_solver                    active
% 7.84/1.50  --res_prop_simpl_new                    false
% 7.84/1.50  --res_prop_simpl_given                  true
% 7.84/1.50  --res_passive_queue_type                priority_queues
% 7.84/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.50  --res_passive_queues_freq               [15;5]
% 7.84/1.50  --res_forward_subs                      full
% 7.84/1.50  --res_backward_subs                     full
% 7.84/1.50  --res_forward_subs_resolution           true
% 7.84/1.50  --res_backward_subs_resolution          true
% 7.84/1.50  --res_orphan_elimination                true
% 7.84/1.50  --res_time_limit                        2.
% 7.84/1.50  --res_out_proof                         true
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Options
% 7.84/1.50  
% 7.84/1.50  --superposition_flag                    true
% 7.84/1.50  --sup_passive_queue_type                priority_queues
% 7.84/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.50  --demod_completeness_check              fast
% 7.84/1.50  --demod_use_ground                      true
% 7.84/1.50  --sup_to_prop_solver                    passive
% 7.84/1.50  --sup_prop_simpl_new                    true
% 7.84/1.50  --sup_prop_simpl_given                  true
% 7.84/1.50  --sup_fun_splitting                     true
% 7.84/1.50  --sup_smt_interval                      50000
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Simplification Setup
% 7.84/1.50  
% 7.84/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.50  --sup_immed_triv                        [TrivRules]
% 7.84/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_bw_main                     []
% 7.84/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_input_bw                          []
% 7.84/1.50  
% 7.84/1.50  ------ Combination Options
% 7.84/1.50  
% 7.84/1.50  --comb_res_mult                         3
% 7.84/1.50  --comb_sup_mult                         2
% 7.84/1.50  --comb_inst_mult                        10
% 7.84/1.50  
% 7.84/1.50  ------ Debug Options
% 7.84/1.50  
% 7.84/1.50  --dbg_backtrace                         false
% 7.84/1.50  --dbg_dump_prop_clauses                 false
% 7.84/1.50  --dbg_dump_prop_clauses_file            -
% 7.84/1.50  --dbg_out_stat                          false
% 7.84/1.50  ------ Parsing...
% 7.84/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.50  ------ Proving...
% 7.84/1.50  ------ Problem Properties 
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  clauses                                 40
% 7.84/1.50  conjectures                             3
% 7.84/1.50  EPR                                     12
% 7.84/1.50  Horn                                    28
% 7.84/1.50  unary                                   9
% 7.84/1.50  binary                                  9
% 7.84/1.50  lits                                    101
% 7.84/1.50  lits eq                                 10
% 7.84/1.50  fd_pure                                 0
% 7.84/1.50  fd_pseudo                               0
% 7.84/1.50  fd_cond                                 3
% 7.84/1.50  fd_pseudo_cond                          1
% 7.84/1.50  AC symbols                              0
% 7.84/1.50  
% 7.84/1.50  ------ Schedule dynamic 5 is on 
% 7.84/1.50  
% 7.84/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ 
% 7.84/1.50  Current options:
% 7.84/1.50  ------ 
% 7.84/1.50  
% 7.84/1.50  ------ Input Options
% 7.84/1.50  
% 7.84/1.50  --out_options                           all
% 7.84/1.50  --tptp_safe_out                         true
% 7.84/1.50  --problem_path                          ""
% 7.84/1.50  --include_path                          ""
% 7.84/1.50  --clausifier                            res/vclausify_rel
% 7.84/1.50  --clausifier_options                    ""
% 7.84/1.50  --stdin                                 false
% 7.84/1.50  --stats_out                             all
% 7.84/1.50  
% 7.84/1.50  ------ General Options
% 7.84/1.50  
% 7.84/1.50  --fof                                   false
% 7.84/1.50  --time_out_real                         305.
% 7.84/1.50  --time_out_virtual                      -1.
% 7.84/1.50  --symbol_type_check                     false
% 7.84/1.50  --clausify_out                          false
% 7.84/1.50  --sig_cnt_out                           false
% 7.84/1.50  --trig_cnt_out                          false
% 7.84/1.50  --trig_cnt_out_tolerance                1.
% 7.84/1.50  --trig_cnt_out_sk_spl                   false
% 7.84/1.50  --abstr_cl_out                          false
% 7.84/1.50  
% 7.84/1.50  ------ Global Options
% 7.84/1.50  
% 7.84/1.50  --schedule                              default
% 7.84/1.50  --add_important_lit                     false
% 7.84/1.50  --prop_solver_per_cl                    1000
% 7.84/1.50  --min_unsat_core                        false
% 7.84/1.50  --soft_assumptions                      false
% 7.84/1.50  --soft_lemma_size                       3
% 7.84/1.50  --prop_impl_unit_size                   0
% 7.84/1.50  --prop_impl_unit                        []
% 7.84/1.50  --share_sel_clauses                     true
% 7.84/1.50  --reset_solvers                         false
% 7.84/1.50  --bc_imp_inh                            [conj_cone]
% 7.84/1.50  --conj_cone_tolerance                   3.
% 7.84/1.50  --extra_neg_conj                        none
% 7.84/1.50  --large_theory_mode                     true
% 7.84/1.50  --prolific_symb_bound                   200
% 7.84/1.50  --lt_threshold                          2000
% 7.84/1.50  --clause_weak_htbl                      true
% 7.84/1.50  --gc_record_bc_elim                     false
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing Options
% 7.84/1.50  
% 7.84/1.50  --preprocessing_flag                    true
% 7.84/1.50  --time_out_prep_mult                    0.1
% 7.84/1.50  --splitting_mode                        input
% 7.84/1.50  --splitting_grd                         true
% 7.84/1.50  --splitting_cvd                         false
% 7.84/1.50  --splitting_cvd_svl                     false
% 7.84/1.50  --splitting_nvd                         32
% 7.84/1.50  --sub_typing                            true
% 7.84/1.50  --prep_gs_sim                           true
% 7.84/1.50  --prep_unflatten                        true
% 7.84/1.50  --prep_res_sim                          true
% 7.84/1.50  --prep_upred                            true
% 7.84/1.50  --prep_sem_filter                       exhaustive
% 7.84/1.50  --prep_sem_filter_out                   false
% 7.84/1.50  --pred_elim                             true
% 7.84/1.50  --res_sim_input                         true
% 7.84/1.50  --eq_ax_congr_red                       true
% 7.84/1.50  --pure_diseq_elim                       true
% 7.84/1.50  --brand_transform                       false
% 7.84/1.50  --non_eq_to_eq                          false
% 7.84/1.50  --prep_def_merge                        true
% 7.84/1.50  --prep_def_merge_prop_impl              false
% 7.84/1.50  --prep_def_merge_mbd                    true
% 7.84/1.50  --prep_def_merge_tr_red                 false
% 7.84/1.50  --prep_def_merge_tr_cl                  false
% 7.84/1.50  --smt_preprocessing                     true
% 7.84/1.50  --smt_ac_axioms                         fast
% 7.84/1.50  --preprocessed_out                      false
% 7.84/1.50  --preprocessed_stats                    false
% 7.84/1.50  
% 7.84/1.50  ------ Abstraction refinement Options
% 7.84/1.50  
% 7.84/1.50  --abstr_ref                             []
% 7.84/1.50  --abstr_ref_prep                        false
% 7.84/1.50  --abstr_ref_until_sat                   false
% 7.84/1.50  --abstr_ref_sig_restrict                funpre
% 7.84/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.50  --abstr_ref_under                       []
% 7.84/1.50  
% 7.84/1.50  ------ SAT Options
% 7.84/1.50  
% 7.84/1.50  --sat_mode                              false
% 7.84/1.50  --sat_fm_restart_options                ""
% 7.84/1.50  --sat_gr_def                            false
% 7.84/1.50  --sat_epr_types                         true
% 7.84/1.50  --sat_non_cyclic_types                  false
% 7.84/1.50  --sat_finite_models                     false
% 7.84/1.50  --sat_fm_lemmas                         false
% 7.84/1.50  --sat_fm_prep                           false
% 7.84/1.50  --sat_fm_uc_incr                        true
% 7.84/1.50  --sat_out_model                         small
% 7.84/1.50  --sat_out_clauses                       false
% 7.84/1.50  
% 7.84/1.50  ------ QBF Options
% 7.84/1.50  
% 7.84/1.50  --qbf_mode                              false
% 7.84/1.50  --qbf_elim_univ                         false
% 7.84/1.50  --qbf_dom_inst                          none
% 7.84/1.50  --qbf_dom_pre_inst                      false
% 7.84/1.50  --qbf_sk_in                             false
% 7.84/1.50  --qbf_pred_elim                         true
% 7.84/1.50  --qbf_split                             512
% 7.84/1.50  
% 7.84/1.50  ------ BMC1 Options
% 7.84/1.50  
% 7.84/1.50  --bmc1_incremental                      false
% 7.84/1.50  --bmc1_axioms                           reachable_all
% 7.84/1.50  --bmc1_min_bound                        0
% 7.84/1.50  --bmc1_max_bound                        -1
% 7.84/1.50  --bmc1_max_bound_default                -1
% 7.84/1.50  --bmc1_symbol_reachability              true
% 7.84/1.50  --bmc1_property_lemmas                  false
% 7.84/1.50  --bmc1_k_induction                      false
% 7.84/1.50  --bmc1_non_equiv_states                 false
% 7.84/1.50  --bmc1_deadlock                         false
% 7.84/1.50  --bmc1_ucm                              false
% 7.84/1.50  --bmc1_add_unsat_core                   none
% 7.84/1.50  --bmc1_unsat_core_children              false
% 7.84/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.50  --bmc1_out_stat                         full
% 7.84/1.50  --bmc1_ground_init                      false
% 7.84/1.50  --bmc1_pre_inst_next_state              false
% 7.84/1.50  --bmc1_pre_inst_state                   false
% 7.84/1.50  --bmc1_pre_inst_reach_state             false
% 7.84/1.50  --bmc1_out_unsat_core                   false
% 7.84/1.50  --bmc1_aig_witness_out                  false
% 7.84/1.50  --bmc1_verbose                          false
% 7.84/1.50  --bmc1_dump_clauses_tptp                false
% 7.84/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.50  --bmc1_dump_file                        -
% 7.84/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.50  --bmc1_ucm_extend_mode                  1
% 7.84/1.50  --bmc1_ucm_init_mode                    2
% 7.84/1.50  --bmc1_ucm_cone_mode                    none
% 7.84/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.50  --bmc1_ucm_relax_model                  4
% 7.84/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.50  --bmc1_ucm_layered_model                none
% 7.84/1.50  --bmc1_ucm_max_lemma_size               10
% 7.84/1.50  
% 7.84/1.50  ------ AIG Options
% 7.84/1.50  
% 7.84/1.50  --aig_mode                              false
% 7.84/1.50  
% 7.84/1.50  ------ Instantiation Options
% 7.84/1.50  
% 7.84/1.50  --instantiation_flag                    true
% 7.84/1.50  --inst_sos_flag                         true
% 7.84/1.50  --inst_sos_phase                        true
% 7.84/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.50  --inst_lit_sel_side                     none
% 7.84/1.50  --inst_solver_per_active                1400
% 7.84/1.50  --inst_solver_calls_frac                1.
% 7.84/1.50  --inst_passive_queue_type               priority_queues
% 7.84/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.50  --inst_passive_queues_freq              [25;2]
% 7.84/1.50  --inst_dismatching                      true
% 7.84/1.50  --inst_eager_unprocessed_to_passive     true
% 7.84/1.50  --inst_prop_sim_given                   true
% 7.84/1.50  --inst_prop_sim_new                     false
% 7.84/1.50  --inst_subs_new                         false
% 7.84/1.50  --inst_eq_res_simp                      false
% 7.84/1.50  --inst_subs_given                       false
% 7.84/1.50  --inst_orphan_elimination               true
% 7.84/1.50  --inst_learning_loop_flag               true
% 7.84/1.50  --inst_learning_start                   3000
% 7.84/1.50  --inst_learning_factor                  2
% 7.84/1.50  --inst_start_prop_sim_after_learn       3
% 7.84/1.50  --inst_sel_renew                        solver
% 7.84/1.50  --inst_lit_activity_flag                true
% 7.84/1.50  --inst_restr_to_given                   false
% 7.84/1.50  --inst_activity_threshold               500
% 7.84/1.50  --inst_out_proof                        true
% 7.84/1.50  
% 7.84/1.50  ------ Resolution Options
% 7.84/1.50  
% 7.84/1.50  --resolution_flag                       false
% 7.84/1.50  --res_lit_sel                           adaptive
% 7.84/1.50  --res_lit_sel_side                      none
% 7.84/1.50  --res_ordering                          kbo
% 7.84/1.50  --res_to_prop_solver                    active
% 7.84/1.50  --res_prop_simpl_new                    false
% 7.84/1.50  --res_prop_simpl_given                  true
% 7.84/1.50  --res_passive_queue_type                priority_queues
% 7.84/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.50  --res_passive_queues_freq               [15;5]
% 7.84/1.50  --res_forward_subs                      full
% 7.84/1.50  --res_backward_subs                     full
% 7.84/1.50  --res_forward_subs_resolution           true
% 7.84/1.50  --res_backward_subs_resolution          true
% 7.84/1.50  --res_orphan_elimination                true
% 7.84/1.50  --res_time_limit                        2.
% 7.84/1.50  --res_out_proof                         true
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Options
% 7.84/1.50  
% 7.84/1.50  --superposition_flag                    true
% 7.84/1.50  --sup_passive_queue_type                priority_queues
% 7.84/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.50  --demod_completeness_check              fast
% 7.84/1.50  --demod_use_ground                      true
% 7.84/1.50  --sup_to_prop_solver                    passive
% 7.84/1.50  --sup_prop_simpl_new                    true
% 7.84/1.50  --sup_prop_simpl_given                  true
% 7.84/1.50  --sup_fun_splitting                     true
% 7.84/1.50  --sup_smt_interval                      50000
% 7.84/1.50  
% 7.84/1.50  ------ Superposition Simplification Setup
% 7.84/1.50  
% 7.84/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.50  --sup_immed_triv                        [TrivRules]
% 7.84/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_immed_bw_main                     []
% 7.84/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.50  --sup_input_bw                          []
% 7.84/1.50  
% 7.84/1.50  ------ Combination Options
% 7.84/1.50  
% 7.84/1.50  --comb_res_mult                         3
% 7.84/1.50  --comb_sup_mult                         2
% 7.84/1.50  --comb_inst_mult                        10
% 7.84/1.50  
% 7.84/1.50  ------ Debug Options
% 7.84/1.50  
% 7.84/1.50  --dbg_backtrace                         false
% 7.84/1.50  --dbg_dump_prop_clauses                 false
% 7.84/1.50  --dbg_dump_prop_clauses_file            -
% 7.84/1.50  --dbg_out_stat                          false
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  ------ Proving...
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS status Theorem for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  fof(f2,axiom,(
% 7.84/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f24,plain,(
% 7.84/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f2])).
% 7.84/1.50  
% 7.84/1.50  fof(f47,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.50    inference(nnf_transformation,[],[f24])).
% 7.84/1.50  
% 7.84/1.50  fof(f48,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.50    inference(rectify,[],[f47])).
% 7.84/1.50  
% 7.84/1.50  fof(f49,plain,(
% 7.84/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f50,plain,(
% 7.84/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 7.84/1.50  
% 7.84/1.50  fof(f77,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f50])).
% 7.84/1.50  
% 7.84/1.50  fof(f5,axiom,(
% 7.84/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f25,plain,(
% 7.84/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f5])).
% 7.84/1.50  
% 7.84/1.50  fof(f53,plain,(
% 7.84/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.84/1.50    inference(nnf_transformation,[],[f25])).
% 7.84/1.50  
% 7.84/1.50  fof(f84,plain,(
% 7.84/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f53])).
% 7.84/1.50  
% 7.84/1.50  fof(f1,axiom,(
% 7.84/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f43,plain,(
% 7.84/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.50    inference(nnf_transformation,[],[f1])).
% 7.84/1.50  
% 7.84/1.50  fof(f44,plain,(
% 7.84/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.50    inference(rectify,[],[f43])).
% 7.84/1.50  
% 7.84/1.50  fof(f45,plain,(
% 7.84/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f46,plain,(
% 7.84/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 7.84/1.50  
% 7.84/1.50  fof(f74,plain,(
% 7.84/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f46])).
% 7.84/1.50  
% 7.84/1.50  fof(f12,axiom,(
% 7.84/1.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f32,plain,(
% 7.84/1.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(ennf_transformation,[],[f12])).
% 7.84/1.50  
% 7.84/1.50  fof(f96,plain,(
% 7.84/1.50    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f32])).
% 7.84/1.50  
% 7.84/1.50  fof(f18,conjecture,(
% 7.84/1.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f19,negated_conjecture,(
% 7.84/1.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.84/1.50    inference(negated_conjecture,[],[f18])).
% 7.84/1.50  
% 7.84/1.50  fof(f20,plain,(
% 7.84/1.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.84/1.50    inference(pure_predicate_removal,[],[f19])).
% 7.84/1.50  
% 7.84/1.50  fof(f21,plain,(
% 7.84/1.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.84/1.50    inference(pure_predicate_removal,[],[f20])).
% 7.84/1.50  
% 7.84/1.50  fof(f22,plain,(
% 7.84/1.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 7.84/1.50    inference(pure_predicate_removal,[],[f21])).
% 7.84/1.50  
% 7.84/1.50  fof(f41,plain,(
% 7.84/1.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f22])).
% 7.84/1.50  
% 7.84/1.50  fof(f42,plain,(
% 7.84/1.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.84/1.50    inference(flattening,[],[f41])).
% 7.84/1.50  
% 7.84/1.50  fof(f69,plain,(
% 7.84/1.50    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.84/1.50    inference(nnf_transformation,[],[f42])).
% 7.84/1.50  
% 7.84/1.50  fof(f70,plain,(
% 7.84/1.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 7.84/1.50    inference(flattening,[],[f69])).
% 7.84/1.50  
% 7.84/1.50  fof(f72,plain,(
% 7.84/1.50    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f71,plain,(
% 7.84/1.50    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f73,plain,(
% 7.84/1.50    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f70,f72,f71])).
% 7.84/1.50  
% 7.84/1.50  fof(f115,plain,(
% 7.84/1.50    l1_orders_2(sK6)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f14,axiom,(
% 7.84/1.50    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f35,plain,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(ennf_transformation,[],[f14])).
% 7.84/1.50  
% 7.84/1.50  fof(f102,plain,(
% 7.84/1.50    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f35])).
% 7.84/1.50  
% 7.84/1.50  fof(f11,axiom,(
% 7.84/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f30,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(ennf_transformation,[],[f11])).
% 7.84/1.50  
% 7.84/1.50  fof(f31,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(flattening,[],[f30])).
% 7.84/1.50  
% 7.84/1.50  fof(f54,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(nnf_transformation,[],[f31])).
% 7.84/1.50  
% 7.84/1.50  fof(f55,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(rectify,[],[f54])).
% 7.84/1.50  
% 7.84/1.50  fof(f56,plain,(
% 7.84/1.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f57,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).
% 7.84/1.50  
% 7.84/1.50  fof(f94,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f57])).
% 7.84/1.50  
% 7.84/1.50  fof(f17,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f40,plain,(
% 7.84/1.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f17])).
% 7.84/1.50  
% 7.84/1.50  fof(f68,plain,(
% 7.84/1.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.84/1.50    inference(nnf_transformation,[],[f40])).
% 7.84/1.50  
% 7.84/1.50  fof(f111,plain,(
% 7.84/1.50    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f68])).
% 7.84/1.50  
% 7.84/1.50  fof(f120,plain,(
% 7.84/1.50    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f118,plain,(
% 7.84/1.50    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f13,axiom,(
% 7.84/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f33,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(ennf_transformation,[],[f13])).
% 7.84/1.50  
% 7.84/1.50  fof(f34,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(flattening,[],[f33])).
% 7.84/1.50  
% 7.84/1.50  fof(f58,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(nnf_transformation,[],[f34])).
% 7.84/1.50  
% 7.84/1.50  fof(f59,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(flattening,[],[f58])).
% 7.84/1.50  
% 7.84/1.50  fof(f60,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(rectify,[],[f59])).
% 7.84/1.50  
% 7.84/1.50  fof(f61,plain,(
% 7.84/1.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f62,plain,(
% 7.84/1.50    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).
% 7.84/1.50  
% 7.84/1.50  fof(f98,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f62])).
% 7.84/1.50  
% 7.84/1.50  fof(f123,plain,(
% 7.84/1.50    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(equality_resolution,[],[f98])).
% 7.84/1.50  
% 7.84/1.50  fof(f15,axiom,(
% 7.84/1.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f23,plain,(
% 7.84/1.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 7.84/1.50    inference(pure_predicate_removal,[],[f15])).
% 7.84/1.50  
% 7.84/1.50  fof(f36,plain,(
% 7.84/1.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f23])).
% 7.84/1.50  
% 7.84/1.50  fof(f37,plain,(
% 7.84/1.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 7.84/1.50    inference(flattening,[],[f36])).
% 7.84/1.50  
% 7.84/1.50  fof(f103,plain,(
% 7.84/1.50    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f37])).
% 7.84/1.50  
% 7.84/1.50  fof(f114,plain,(
% 7.84/1.50    v1_yellow_0(sK6)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f112,plain,(
% 7.84/1.50    ~v2_struct_0(sK6)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f113,plain,(
% 7.84/1.50    v5_orders_2(sK6)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f16,axiom,(
% 7.84/1.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f38,plain,(
% 7.84/1.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(ennf_transformation,[],[f16])).
% 7.84/1.50  
% 7.84/1.50  fof(f39,plain,(
% 7.84/1.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(flattening,[],[f38])).
% 7.84/1.50  
% 7.84/1.50  fof(f63,plain,(
% 7.84/1.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(nnf_transformation,[],[f39])).
% 7.84/1.50  
% 7.84/1.50  fof(f64,plain,(
% 7.84/1.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(rectify,[],[f63])).
% 7.84/1.50  
% 7.84/1.50  fof(f66,plain,(
% 7.84/1.50    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f65,plain,(
% 7.84/1.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 7.84/1.50    introduced(choice_axiom,[])).
% 7.84/1.50  
% 7.84/1.50  fof(f67,plain,(
% 7.84/1.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 7.84/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).
% 7.84/1.50  
% 7.84/1.50  fof(f104,plain,(
% 7.84/1.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f67])).
% 7.84/1.50  
% 7.84/1.50  fof(f9,axiom,(
% 7.84/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f27,plain,(
% 7.84/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.84/1.50    inference(ennf_transformation,[],[f9])).
% 7.84/1.50  
% 7.84/1.50  fof(f28,plain,(
% 7.84/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.84/1.50    inference(flattening,[],[f27])).
% 7.84/1.50  
% 7.84/1.50  fof(f90,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f28])).
% 7.84/1.50  
% 7.84/1.50  fof(f117,plain,(
% 7.84/1.50    v13_waybel_0(sK7,sK6)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f116,plain,(
% 7.84/1.50    ~v1_xboole_0(sK7)),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f4,axiom,(
% 7.84/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f51,plain,(
% 7.84/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.50    inference(nnf_transformation,[],[f4])).
% 7.84/1.50  
% 7.84/1.50  fof(f52,plain,(
% 7.84/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.84/1.50    inference(flattening,[],[f51])).
% 7.84/1.50  
% 7.84/1.50  fof(f80,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.84/1.50    inference(cnf_transformation,[],[f52])).
% 7.84/1.50  
% 7.84/1.50  fof(f122,plain,(
% 7.84/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.84/1.50    inference(equality_resolution,[],[f80])).
% 7.84/1.50  
% 7.84/1.50  fof(f82,plain,(
% 7.84/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f52])).
% 7.84/1.50  
% 7.84/1.50  fof(f75,plain,(
% 7.84/1.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f46])).
% 7.84/1.50  
% 7.84/1.50  fof(f7,axiom,(
% 7.84/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f26,plain,(
% 7.84/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.84/1.50    inference(ennf_transformation,[],[f7])).
% 7.84/1.50  
% 7.84/1.50  fof(f88,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.84/1.50    inference(cnf_transformation,[],[f26])).
% 7.84/1.50  
% 7.84/1.50  fof(f81,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.84/1.50    inference(cnf_transformation,[],[f52])).
% 7.84/1.50  
% 7.84/1.50  fof(f121,plain,(
% 7.84/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.84/1.50    inference(equality_resolution,[],[f81])).
% 7.84/1.50  
% 7.84/1.50  fof(f83,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f53])).
% 7.84/1.50  
% 7.84/1.50  fof(f3,axiom,(
% 7.84/1.50    v1_xboole_0(k1_xboole_0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f79,plain,(
% 7.84/1.50    v1_xboole_0(k1_xboole_0)),
% 7.84/1.50    inference(cnf_transformation,[],[f3])).
% 7.84/1.50  
% 7.84/1.50  fof(f92,plain,(
% 7.84/1.50    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f57])).
% 7.84/1.50  
% 7.84/1.50  fof(f97,plain,(
% 7.84/1.50    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f62])).
% 7.84/1.50  
% 7.84/1.50  fof(f124,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 7.84/1.50    inference(equality_resolution,[],[f97])).
% 7.84/1.50  
% 7.84/1.50  fof(f78,plain,(
% 7.84/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f50])).
% 7.84/1.50  
% 7.84/1.50  fof(f8,axiom,(
% 7.84/1.50    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f89,plain,(
% 7.84/1.50    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f8])).
% 7.84/1.50  
% 7.84/1.50  fof(f119,plain,(
% 7.84/1.50    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 7.84/1.50    inference(cnf_transformation,[],[f73])).
% 7.84/1.50  
% 7.84/1.50  fof(f6,axiom,(
% 7.84/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.50  
% 7.84/1.50  fof(f87,plain,(
% 7.84/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.84/1.50    inference(cnf_transformation,[],[f6])).
% 7.84/1.50  
% 7.84/1.50  fof(f76,plain,(
% 7.84/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.84/1.50    inference(cnf_transformation,[],[f50])).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3,plain,
% 7.84/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2744,plain,
% 7.84/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.84/1.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_11,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_291,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_11,c_1]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_292,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_291]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2730,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.84/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7604,plain,
% 7.84/1.50      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 7.84/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2744,c_2730]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22,plain,
% 7.84/1.50      ( ~ l1_orders_2(X0)
% 7.84/1.50      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_43,negated_conjecture,
% 7.84/1.50      ( l1_orders_2(sK6) ),
% 7.84/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_857,plain,
% 7.84/1.50      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_858,plain,
% 7.84/1.50      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_857]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_28,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_848,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_849,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_848]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2718,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_19,plain,
% 7.84/1.50      ( r2_lattice3(X0,X1,X2)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | r2_hidden(sK2(X0,X1,X2),X1)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_898,plain,
% 7.84/1.50      ( r2_lattice3(X0,X1,X2)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | r2_hidden(sK2(X0,X1,X2),X1)
% 7.84/1.50      | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_899,plain,
% 7.84/1.50      ( r2_lattice3(sK6,X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_898]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2715,plain,
% 7.84/1.50      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2746,plain,
% 7.84/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.84/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4041,plain,
% 7.84/1.50      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2715,c_2746]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4222,plain,
% 7.84/1.50      ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X1)) = iProver_top
% 7.84/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2718,c_4041]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_36,plain,
% 7.84/1.50      ( v1_subset_1(X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.84/1.50      | X0 = X1 ),
% 7.84/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_38,negated_conjecture,
% 7.84/1.50      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_366,plain,
% 7.84/1.50      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(prop_impl,[status(thm)],[c_38]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_643,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.84/1.50      | X1 = X0
% 7.84/1.50      | u1_struct_0(sK6) != X1
% 7.84/1.50      | sK7 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_36,c_366]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_644,plain,
% 7.84/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.84/1.50      | u1_struct_0(sK6) = sK7 ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_643]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_40,negated_conjecture,
% 7.84/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 7.84/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_646,plain,
% 7.84/1.50      ( r2_hidden(k3_yellow_0(sK6),sK7) | u1_struct_0(sK6) = sK7 ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_644,c_40]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2727,plain,
% 7.84/1.50      ( u1_struct_0(sK6) = sK7
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_26,plain,
% 7.84/1.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.84/1.50      | ~ r2_lattice3(X0,X1,X2)
% 7.84/1.50      | ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_271,plain,
% 7.84/1.50      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | ~ r2_lattice3(X0,X1,X2)
% 7.84/1.50      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_26,c_28]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_272,plain,
% 7.84/1.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.84/1.50      | ~ r2_lattice3(X0,X1,X2)
% 7.84/1.50      | ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_271]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_29,plain,
% 7.84/1.50      ( r1_yellow_0(X0,k1_xboole_0)
% 7.84/1.50      | v2_struct_0(X0)
% 7.84/1.50      | ~ v5_orders_2(X0)
% 7.84/1.50      | ~ v1_yellow_0(X0)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_44,negated_conjecture,
% 7.84/1.50      ( v1_yellow_0(sK6) ),
% 7.84/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_605,plain,
% 7.84/1.50      ( r1_yellow_0(X0,k1_xboole_0)
% 7.84/1.50      | v2_struct_0(X0)
% 7.84/1.50      | ~ v5_orders_2(X0)
% 7.84/1.50      | ~ l1_orders_2(X0)
% 7.84/1.50      | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_29,c_44]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_606,plain,
% 7.84/1.50      ( r1_yellow_0(sK6,k1_xboole_0)
% 7.84/1.50      | v2_struct_0(sK6)
% 7.84/1.50      | ~ v5_orders_2(sK6)
% 7.84/1.50      | ~ l1_orders_2(sK6) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_605]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_46,negated_conjecture,
% 7.84/1.50      ( ~ v2_struct_0(sK6) ),
% 7.84/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_45,negated_conjecture,
% 7.84/1.50      ( v5_orders_2(sK6) ),
% 7.84/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_79,plain,
% 7.84/1.50      ( r1_yellow_0(sK6,k1_xboole_0)
% 7.84/1.50      | v2_struct_0(sK6)
% 7.84/1.50      | ~ v5_orders_2(sK6)
% 7.84/1.50      | ~ v1_yellow_0(sK6)
% 7.84/1.50      | ~ l1_orders_2(sK6) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_608,plain,
% 7.84/1.50      ( r1_yellow_0(sK6,k1_xboole_0) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_606,c_46,c_45,c_44,c_43,c_79]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_707,plain,
% 7.84/1.50      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 7.84/1.50      | ~ r2_lattice3(X0,X1,X2)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ l1_orders_2(X0)
% 7.84/1.50      | sK6 != X0
% 7.84/1.50      | k1_xboole_0 != X1 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_272,c_608]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_708,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 7.84/1.50      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ l1_orders_2(sK6) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_707]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_712,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.84/1.50      | r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_708,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_713,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 7.84/1.50      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_712]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2724,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2752,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(light_normalisation,[status(thm)],[c_2724,c_858]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2733,plain,
% 7.84/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_35,plain,
% 7.84/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.84/1.50      | ~ v13_waybel_0(X3,X0)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.84/1.50      | ~ r2_hidden(X1,X3)
% 7.84/1.50      | r2_hidden(X2,X3)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_808,plain,
% 7.84/1.50      ( ~ r1_orders_2(X0,X1,X2)
% 7.84/1.50      | ~ v13_waybel_0(X3,X0)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.84/1.50      | ~ r2_hidden(X1,X3)
% 7.84/1.50      | r2_hidden(X2,X3)
% 7.84/1.50      | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_35,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_809,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ v13_waybel_0(X2,sK6)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X0,X2)
% 7.84/1.50      | r2_hidden(X1,X2) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_808]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_16,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.84/1.50      | ~ r2_hidden(X0,X2) ),
% 7.84/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_825,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ v13_waybel_0(X2,sK6)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X0,X2)
% 7.84/1.50      | r2_hidden(X1,X2) ),
% 7.84/1.50      inference(forward_subsumption_resolution,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_809,c_16]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2720,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.84/1.50      | v13_waybel_0(X2,sK6) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.84/1.50      | r2_hidden(X0,X2) != iProver_top
% 7.84/1.50      | r2_hidden(X1,X2) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4459,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.84/1.50      | v13_waybel_0(sK7,sK6) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.84/1.50      | r2_hidden(X1,sK7) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2733,c_2720]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_53,plain,
% 7.84/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_41,negated_conjecture,
% 7.84/1.50      ( v13_waybel_0(sK7,sK6) ),
% 7.84/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1036,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X0,X2)
% 7.84/1.50      | r2_hidden(X1,X2)
% 7.84/1.50      | sK7 != X2
% 7.84/1.50      | sK6 != sK6 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_41,c_825]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1037,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X0,sK7)
% 7.84/1.50      | r2_hidden(X1,sK7) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_1036]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_1038,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.84/1.50      | r2_hidden(X1,sK7) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4752,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.84/1.50      | r2_hidden(X1,sK7) = iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_4459,c_53,c_1038]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4757,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2752,c_4752]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6100,plain,
% 7.84/1.50      ( u1_struct_0(sK6) = sK7
% 7.84/1.50      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2727,c_4757]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_42,negated_conjecture,
% 7.84/1.50      ( ~ v1_xboole_0(sK7) ),
% 7.84/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_51,plain,
% 7.84/1.50      ( v1_xboole_0(sK7) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_52,plain,
% 7.84/1.50      ( v13_waybel_0(sK7,sK6) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_8,plain,
% 7.84/1.50      ( r1_tarski(X0,X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_136,plain,
% 7.84/1.50      ( r1_tarski(sK6,sK6) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_140,plain,
% 7.84/1.50      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2084,plain,
% 7.84/1.50      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 7.84/1.50      theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2099,plain,
% 7.84/1.50      ( k3_yellow_0(sK6) = k3_yellow_0(sK6) | sK6 != sK6 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_2084]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_0,plain,
% 7.84/1.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2821,plain,
% 7.84/1.50      ( r2_hidden(sK0(sK7),sK7) | v1_xboole_0(sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2822,plain,
% 7.84/1.50      ( r2_hidden(sK0(sK7),sK7) = iProver_top
% 7.84/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_2821]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2953,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ v13_waybel_0(sK7,sK6)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X0,sK7)
% 7.84/1.50      | r2_hidden(X1,sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_825]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3050,plain,
% 7.84/1.50      ( ~ r1_orders_2(sK6,k3_yellow_0(sK6),X0)
% 7.84/1.50      | ~ v13_waybel_0(sK7,sK6)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | r2_hidden(X0,sK7)
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_2953]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3051,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) != iProver_top
% 7.84/1.50      | v13_waybel_0(sK7,sK6) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_3050]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3005,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3345,plain,
% 7.84/1.50      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3005]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_14,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.84/1.50      | ~ r2_hidden(X2,X0)
% 7.84/1.50      | r2_hidden(X2,X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3062,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | ~ r2_hidden(X1,X0)
% 7.84/1.50      | r2_hidden(X1,u1_struct_0(sK6)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3611,plain,
% 7.84/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | r2_hidden(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_hidden(X0,sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3062]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3871,plain,
% 7.84/1.50      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 7.84/1.50      | r2_hidden(sK0(sK7),u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_hidden(sK0(sK7),sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3611]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3872,plain,
% 7.84/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 7.84/1.50      | r2_hidden(sK0(sK7),u1_struct_0(sK6)) = iProver_top
% 7.84/1.50      | r2_hidden(sK0(sK7),sK7) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_3871]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7,plain,
% 7.84/1.50      ( r1_tarski(X0,X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4098,plain,
% 7.84/1.50      ( r1_tarski(sK7,sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3130,plain,
% 7.84/1.50      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_858,c_2718]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_12,plain,
% 7.84/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2737,plain,
% 7.84/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.84/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.84/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4539,plain,
% 7.84/1.50      ( r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top
% 7.84/1.50      | v1_xboole_0(u1_struct_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_3130,c_2737]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3495,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4801,plain,
% 7.84/1.50      ( ~ r2_hidden(sK0(sK7),u1_struct_0(sK6))
% 7.84/1.50      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3495]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4805,plain,
% 7.84/1.50      ( r2_hidden(sK0(sK7),u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_4801]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2074,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3004,plain,
% 7.84/1.50      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_2074]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3360,plain,
% 7.84/1.50      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3004]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6617,plain,
% 7.84/1.50      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3360]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2076,plain,
% 7.84/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.50      theory(equality) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4823,plain,
% 7.84/1.50      ( r2_hidden(X0,X1)
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
% 7.84/1.50      | X0 != k3_yellow_0(sK6)
% 7.84/1.50      | X1 != u1_struct_0(sK6) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_2076]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6509,plain,
% 7.84/1.50      ( r2_hidden(k3_yellow_0(sK6),X0)
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
% 7.84/1.50      | X0 != u1_struct_0(sK6)
% 7.84/1.50      | k3_yellow_0(sK6) != k3_yellow_0(sK6) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_4823]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_12390,plain,
% 7.84/1.50      ( ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7)
% 7.84/1.50      | k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 7.84/1.50      | sK7 != u1_struct_0(sK6) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_6509]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_12391,plain,
% 7.84/1.50      ( k3_yellow_0(sK6) != k3_yellow_0(sK6)
% 7.84/1.50      | sK7 != u1_struct_0(sK6)
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_12390]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15908,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_6100,c_51,c_52,c_53,c_136,c_140,c_2099,c_2752,c_2822,
% 7.84/1.50                 c_3051,c_3345,c_3872,c_4098,c_4539,c_4805,c_6617,
% 7.84/1.50                 c_12391]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15919,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 7.84/1.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_4222,c_15908]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5,plain,
% 7.84/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_142,plain,
% 7.84/1.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_850,plain,
% 7.84/1.50      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_21476,plain,
% 7.84/1.50      ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_15919,c_142,c_850]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_21,plain,
% 7.84/1.50      ( r1_orders_2(X0,X1,X2)
% 7.84/1.50      | ~ r2_lattice3(X0,X3,X2)
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.84/1.50      | ~ r2_hidden(X1,X3)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_862,plain,
% 7.84/1.50      ( r1_orders_2(X0,X1,X2)
% 7.84/1.50      | ~ r2_lattice3(X0,X3,X2)
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.84/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.84/1.50      | ~ r2_hidden(X1,X3)
% 7.84/1.50      | sK6 != X0 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_863,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1)
% 7.84/1.50      | ~ r2_lattice3(sK6,X2,X1)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_hidden(X0,X2) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_862]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2717,plain,
% 7.84/1.50      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,X2,X1) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3683,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,X2,X1) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(k1_yellow_0(sK6,X0),X2) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2718,c_2717]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_21485,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,sK7,X1) != iProver_top
% 7.84/1.50      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_21476,c_3683]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_21493,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 7.84/1.50      | r2_lattice3(sK6,sK7,X0) != iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_858,c_21485]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3276,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,X0)
% 7.84/1.50      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_899]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3277,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_3276]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_20559,plain,
% 7.84/1.50      ( ~ r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0)
% 7.84/1.50      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_20560,plain,
% 7.84/1.50      ( r2_hidden(sK2(sK6,k1_xboole_0,X0),k1_xboole_0) != iProver_top
% 7.84/1.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_20559]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22177,plain,
% 7.84/1.50      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_21493,c_142,c_2752,c_3277,c_20560]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22184,plain,
% 7.84/1.50      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_22177,c_4752]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_27,plain,
% 7.84/1.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.84/1.50      | ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_264,plain,
% 7.84/1.50      ( ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_27,c_28]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_265,plain,
% 7.84/1.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.84/1.50      | ~ r1_yellow_0(X0,X1)
% 7.84/1.50      | ~ l1_orders_2(X0) ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_264]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_728,plain,
% 7.84/1.50      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 7.84/1.50      | ~ l1_orders_2(X0)
% 7.84/1.50      | sK6 != X0
% 7.84/1.50      | k1_xboole_0 != X1 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_265,c_608]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_729,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0))
% 7.84/1.50      | ~ l1_orders_2(sK6) ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_728]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_731,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_729,c_43]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2723,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,k1_xboole_0)) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2748,plain,
% 7.84/1.50      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(light_normalisation,[status(thm)],[c_2723,c_858]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15918,plain,
% 7.84/1.50      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2748,c_15908]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22437,plain,
% 7.84/1.50      ( r2_hidden(X0,sK7) = iProver_top
% 7.84/1.50      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_22184,c_3130,c_15918]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22438,plain,
% 7.84/1.50      ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) = iProver_top ),
% 7.84/1.50      inference(renaming,[status(thm)],[c_22437]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_22452,plain,
% 7.84/1.50      ( r1_tarski(u1_struct_0(sK6),X0) = iProver_top
% 7.84/1.50      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_7604,c_22438]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2,plain,
% 7.84/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2745,plain,
% 7.84/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.84/1.50      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_25530,plain,
% 7.84/1.50      ( r1_tarski(u1_struct_0(sK6),sK7) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_22452,c_2745]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2736,plain,
% 7.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.84/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.84/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5661,plain,
% 7.84/1.50      ( r2_hidden(X0,u1_struct_0(sK6)) = iProver_top
% 7.84/1.50      | r2_hidden(X0,sK7) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2733,c_2736]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5738,plain,
% 7.84/1.50      ( r1_tarski(X0,u1_struct_0(sK6)) = iProver_top
% 7.84/1.50      | r2_hidden(sK1(X0,u1_struct_0(sK6)),sK7) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_5661,c_2745]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_5747,plain,
% 7.84/1.50      ( r1_tarski(sK7,u1_struct_0(sK6)) = iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_2744,c_5738]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2741,plain,
% 7.84/1.50      ( X0 = X1
% 7.84/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.84/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_6449,plain,
% 7.84/1.50      ( u1_struct_0(sK6) = sK7
% 7.84/1.50      | r1_tarski(u1_struct_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(superposition,[status(thm)],[c_5747,c_2741]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_15,plain,
% 7.84/1.50      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 7.84/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_39,negated_conjecture,
% 7.84/1.50      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_364,plain,
% 7.84/1.50      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(prop_impl,[status(thm)],[c_39]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_631,plain,
% 7.84/1.50      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.84/1.50      | u1_struct_0(sK6) != X0
% 7.84/1.50      | k2_subset_1(X0) != sK7 ),
% 7.84/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_364]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_632,plain,
% 7.84/1.50      ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 7.84/1.50      | k2_subset_1(u1_struct_0(sK6)) != sK7 ),
% 7.84/1.50      inference(unflattening,[status(thm)],[c_631]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2728,plain,
% 7.84/1.50      ( k2_subset_1(u1_struct_0(sK6)) != sK7
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_13,plain,
% 7.84/1.50      ( k2_subset_1(X0) = X0 ),
% 7.84/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_2751,plain,
% 7.84/1.50      ( u1_struct_0(sK6) != sK7
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(demodulation,[status(thm)],[c_2728,c_13]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.84/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_3036,plain,
% 7.84/1.50      ( ~ r1_tarski(X0,sK7) | ~ r2_hidden(X1,X0) | r2_hidden(X1,sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4818,plain,
% 7.84/1.50      ( ~ r1_tarski(u1_struct_0(sK6),sK7)
% 7.84/1.50      | ~ r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6))
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 7.84/1.50      inference(instantiation,[status(thm)],[c_3036]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_4819,plain,
% 7.84/1.50      ( r1_tarski(u1_struct_0(sK6),sK7) != iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top
% 7.84/1.50      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 7.84/1.50      inference(predicate_to_equality,[status(thm)],[c_4818]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(c_7731,plain,
% 7.84/1.50      ( r1_tarski(u1_struct_0(sK6),sK7) != iProver_top ),
% 7.84/1.50      inference(global_propositional_subsumption,
% 7.84/1.50                [status(thm)],
% 7.84/1.50                [c_6449,c_51,c_53,c_2751,c_2822,c_3872,c_4539,c_4805,
% 7.84/1.50                 c_4819]) ).
% 7.84/1.50  
% 7.84/1.50  cnf(contradiction,plain,
% 7.84/1.50      ( $false ),
% 7.84/1.50      inference(minisat,[status(thm)],[c_25530,c_7731]) ).
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.50  
% 7.84/1.50  ------                               Statistics
% 7.84/1.50  
% 7.84/1.50  ------ General
% 7.84/1.50  
% 7.84/1.50  abstr_ref_over_cycles:                  0
% 7.84/1.50  abstr_ref_under_cycles:                 0
% 7.84/1.50  gc_basic_clause_elim:                   0
% 7.84/1.50  forced_gc_time:                         0
% 7.84/1.50  parsing_time:                           0.011
% 7.84/1.50  unif_index_cands_time:                  0.
% 7.84/1.50  unif_index_add_time:                    0.
% 7.84/1.50  orderings_time:                         0.
% 7.84/1.50  out_proof_time:                         0.016
% 7.84/1.50  total_time:                             0.734
% 7.84/1.50  num_of_symbols:                         58
% 7.84/1.50  num_of_terms:                           21827
% 7.84/1.50  
% 7.84/1.50  ------ Preprocessing
% 7.84/1.50  
% 7.84/1.50  num_of_splits:                          0
% 7.84/1.50  num_of_split_atoms:                     0
% 7.84/1.50  num_of_reused_defs:                     0
% 7.84/1.50  num_eq_ax_congr_red:                    41
% 7.84/1.50  num_of_sem_filtered_clauses:            1
% 7.84/1.50  num_of_subtypes:                        0
% 7.84/1.50  monotx_restored_types:                  0
% 7.84/1.50  sat_num_of_epr_types:                   0
% 7.84/1.50  sat_num_of_non_cyclic_types:            0
% 7.84/1.50  sat_guarded_non_collapsed_types:        0
% 7.84/1.50  num_pure_diseq_elim:                    0
% 7.84/1.50  simp_replaced_by:                       0
% 7.84/1.50  res_preprocessed:                       201
% 7.84/1.50  prep_upred:                             0
% 7.84/1.50  prep_unflattend:                        69
% 7.84/1.50  smt_new_axioms:                         0
% 7.84/1.50  pred_elim_cands:                        7
% 7.84/1.50  pred_elim:                              6
% 7.84/1.50  pred_elim_cl:                           6
% 7.84/1.50  pred_elim_cycles:                       10
% 7.84/1.50  merged_defs:                            2
% 7.84/1.50  merged_defs_ncl:                        0
% 7.84/1.50  bin_hyper_res:                          2
% 7.84/1.50  prep_cycles:                            4
% 7.84/1.50  pred_elim_time:                         0.024
% 7.84/1.50  splitting_time:                         0.
% 7.84/1.50  sem_filter_time:                        0.
% 7.84/1.50  monotx_time:                            0.001
% 7.84/1.50  subtype_inf_time:                       0.
% 7.84/1.50  
% 7.84/1.50  ------ Problem properties
% 7.84/1.50  
% 7.84/1.50  clauses:                                40
% 7.84/1.50  conjectures:                            3
% 7.84/1.50  epr:                                    12
% 7.84/1.50  horn:                                   28
% 7.84/1.50  ground:                                 9
% 7.84/1.50  unary:                                  9
% 7.84/1.50  binary:                                 9
% 7.84/1.50  lits:                                   101
% 7.84/1.50  lits_eq:                                10
% 7.84/1.50  fd_pure:                                0
% 7.84/1.50  fd_pseudo:                              0
% 7.84/1.50  fd_cond:                                3
% 7.84/1.50  fd_pseudo_cond:                         1
% 7.84/1.50  ac_symbols:                             0
% 7.84/1.50  
% 7.84/1.50  ------ Propositional Solver
% 7.84/1.50  
% 7.84/1.50  prop_solver_calls:                      30
% 7.84/1.50  prop_fast_solver_calls:                 2700
% 7.84/1.50  smt_solver_calls:                       0
% 7.84/1.50  smt_fast_solver_calls:                  0
% 7.84/1.50  prop_num_of_clauses:                    11881
% 7.84/1.50  prop_preprocess_simplified:             21120
% 7.84/1.50  prop_fo_subsumed:                       115
% 7.84/1.50  prop_solver_time:                       0.
% 7.84/1.50  smt_solver_time:                        0.
% 7.84/1.50  smt_fast_solver_time:                   0.
% 7.84/1.50  prop_fast_solver_time:                  0.
% 7.84/1.50  prop_unsat_core_time:                   0.001
% 7.84/1.50  
% 7.84/1.50  ------ QBF
% 7.84/1.50  
% 7.84/1.50  qbf_q_res:                              0
% 7.84/1.50  qbf_num_tautologies:                    0
% 7.84/1.50  qbf_prep_cycles:                        0
% 7.84/1.50  
% 7.84/1.50  ------ BMC1
% 7.84/1.50  
% 7.84/1.50  bmc1_current_bound:                     -1
% 7.84/1.50  bmc1_last_solved_bound:                 -1
% 7.84/1.50  bmc1_unsat_core_size:                   -1
% 7.84/1.50  bmc1_unsat_core_parents_size:           -1
% 7.84/1.50  bmc1_merge_next_fun:                    0
% 7.84/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.84/1.50  
% 7.84/1.50  ------ Instantiation
% 7.84/1.50  
% 7.84/1.50  inst_num_of_clauses:                    2921
% 7.84/1.50  inst_num_in_passive:                    477
% 7.84/1.50  inst_num_in_active:                     1059
% 7.84/1.50  inst_num_in_unprocessed:                1385
% 7.84/1.50  inst_num_of_loops:                      1340
% 7.84/1.50  inst_num_of_learning_restarts:          0
% 7.84/1.50  inst_num_moves_active_passive:          280
% 7.84/1.50  inst_lit_activity:                      0
% 7.84/1.50  inst_lit_activity_moves:                1
% 7.84/1.50  inst_num_tautologies:                   0
% 7.84/1.50  inst_num_prop_implied:                  0
% 7.84/1.50  inst_num_existing_simplified:           0
% 7.84/1.50  inst_num_eq_res_simplified:             0
% 7.84/1.50  inst_num_child_elim:                    0
% 7.84/1.50  inst_num_of_dismatching_blockings:      1360
% 7.84/1.50  inst_num_of_non_proper_insts:           3280
% 7.84/1.50  inst_num_of_duplicates:                 0
% 7.84/1.50  inst_inst_num_from_inst_to_res:         0
% 7.84/1.50  inst_dismatching_checking_time:         0.
% 7.84/1.50  
% 7.84/1.50  ------ Resolution
% 7.84/1.50  
% 7.84/1.50  res_num_of_clauses:                     0
% 7.84/1.50  res_num_in_passive:                     0
% 7.84/1.50  res_num_in_active:                      0
% 7.84/1.50  res_num_of_loops:                       205
% 7.84/1.50  res_forward_subset_subsumed:            226
% 7.84/1.50  res_backward_subset_subsumed:           2
% 7.84/1.50  res_forward_subsumed:                   0
% 7.84/1.50  res_backward_subsumed:                  0
% 7.84/1.50  res_forward_subsumption_resolution:     6
% 7.84/1.50  res_backward_subsumption_resolution:    0
% 7.84/1.50  res_clause_to_clause_subsumption:       6079
% 7.84/1.50  res_orphan_elimination:                 0
% 7.84/1.50  res_tautology_del:                      268
% 7.84/1.50  res_num_eq_res_simplified:              0
% 7.84/1.50  res_num_sel_changes:                    0
% 7.84/1.50  res_moves_from_active_to_pass:          0
% 7.84/1.50  
% 7.84/1.50  ------ Superposition
% 7.84/1.50  
% 7.84/1.50  sup_time_total:                         0.
% 7.84/1.50  sup_time_generating:                    0.
% 7.84/1.50  sup_time_sim_full:                      0.
% 7.84/1.50  sup_time_sim_immed:                     0.
% 7.84/1.50  
% 7.84/1.50  sup_num_of_clauses:                     805
% 7.84/1.50  sup_num_in_active:                      234
% 7.84/1.50  sup_num_in_passive:                     571
% 7.84/1.50  sup_num_of_loops:                       267
% 7.84/1.50  sup_fw_superposition:                   510
% 7.84/1.50  sup_bw_superposition:                   628
% 7.84/1.50  sup_immediate_simplified:               215
% 7.84/1.50  sup_given_eliminated:                   0
% 7.84/1.50  comparisons_done:                       0
% 7.84/1.50  comparisons_avoided:                    0
% 7.84/1.50  
% 7.84/1.50  ------ Simplifications
% 7.84/1.50  
% 7.84/1.50  
% 7.84/1.50  sim_fw_subset_subsumed:                 99
% 7.84/1.50  sim_bw_subset_subsumed:                 21
% 7.84/1.50  sim_fw_subsumed:                        105
% 7.84/1.50  sim_bw_subsumed:                        34
% 7.84/1.50  sim_fw_subsumption_res:                 0
% 7.84/1.50  sim_bw_subsumption_res:                 0
% 7.84/1.50  sim_tautology_del:                      20
% 7.84/1.50  sim_eq_tautology_del:                   10
% 7.84/1.50  sim_eq_res_simp:                        0
% 7.84/1.50  sim_fw_demodulated:                     5
% 7.84/1.50  sim_bw_demodulated:                     0
% 7.84/1.50  sim_light_normalised:                   7
% 7.84/1.50  sim_joinable_taut:                      0
% 7.84/1.50  sim_joinable_simp:                      0
% 7.84/1.50  sim_ac_normalised:                      0
% 7.84/1.50  sim_smt_subsumption:                    0
% 7.84/1.50  
%------------------------------------------------------------------------------
