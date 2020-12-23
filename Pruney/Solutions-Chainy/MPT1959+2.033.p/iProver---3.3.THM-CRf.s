%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:31 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  197 (2239 expanded)
%              Number of clauses        :  113 ( 522 expanded)
%              Number of leaves         :   26 ( 438 expanded)
%              Depth                    :   28
%              Number of atoms          :  840 (18193 expanded)
%              Number of equality atoms :  183 ( 636 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(flattening,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK0(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f37])).

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
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).

fof(f94,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f28])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f87,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK1(X0),X0)
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f43])).

fof(f66,plain,(
    ! [X0] : ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0,X2),X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1912,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_23,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,negated_conjecture,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_269,plain,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | X1 = X0
    | u1_struct_0(sK5) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_269])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) = sK6 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_514,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_27])).

cnf(c_1905,plain,
    ( u1_struct_0(sK5) = sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_16,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_774,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_775,plain,
    ( r2_lattice3(sK5,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_14,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_14])).

cnf(c_211,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_15,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( v1_yellow_0(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_474,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_475,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_32,negated_conjecture,
    ( v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_69,plain,
    ( r1_yellow_0(sK5,k1_xboole_0)
    | v2_struct_0(sK5)
    | ~ v5_orders_2(sK5)
    | ~ v1_yellow_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_477,plain,
    ( r1_yellow_0(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_33,c_32,c_31,c_30,c_69])).

cnf(c_549,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK5 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_477])).

cnf(c_550,plain,
    ( ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ r2_lattice3(sK5,k1_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_30])).

cnf(c_555,plain,
    ( ~ r2_lattice3(sK5,k1_xboole_0,X0)
    | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_554])).

cnf(c_828,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_775,c_555])).

cnf(c_1896,plain,
    ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_8,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_795,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_796,plain,
    ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
    inference(unflattening,[status(thm)],[c_795])).

cnf(c_1942,plain,
    ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1896,c_796])).

cnf(c_1909,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_734,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_735,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_751,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ v13_waybel_0(X2,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_735,c_7])).

cnf(c_1899,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2876,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | v13_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1899])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_936,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK6 != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_751])).

cnf(c_937,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,X1)
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_937,c_27])).

cnf(c_940,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6) ),
    inference(renaming,[status(thm)],[c_939])).

cnf(c_941,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(c_3084,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2876,c_941])).

cnf(c_3093,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1942,c_3084])).

cnf(c_3574,plain,
    ( u1_struct_0(sK5) = sK6
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1905,c_3093])).

cnf(c_1504,plain,
    ( X0 != X1
    | k3_yellow_0(X0) = k3_yellow_0(X1) ),
    theory(equality)).

cnf(c_1516,plain,
    ( k3_yellow_0(sK5) = k3_yellow_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_1498,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1525,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_786,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_787,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_1897,plain,
    ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_2150,plain,
    ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_1897])).

cnf(c_2244,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_1499,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2224,plain,
    ( u1_struct_0(sK5) != X0
    | sK6 != X0
    | sK6 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_2644,plain,
    ( u1_struct_0(sK5) != sK6
    | sK6 = u1_struct_0(sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2698,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X1 != u1_struct_0(sK5)
    | X0 != k3_yellow_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_3026,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | X0 != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2698])).

cnf(c_4032,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
    | m1_subset_1(k3_yellow_0(sK5),sK6)
    | k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_4034,plain,
    ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
    | sK6 != u1_struct_0(sK5)
    | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4032])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,sK6)
    | r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_5673,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
    | r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_5674,plain,
    ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
    | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5673])).

cnf(c_5882,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_1516,c_1525,c_2150,c_2244,c_2644,c_3093,c_4034,c_5674])).

cnf(c_5890,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK5),X1,X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_5882])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2433,plain,
    ( r2_hidden(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1915])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK0(X1,X0,X2),X2)
    | ~ r2_hidden(sK0(X1,X0,X2),X0)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1914,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
    | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2914,plain,
    ( u1_struct_0(sK5) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(sK0(X1,X0,u1_struct_0(sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_1914])).

cnf(c_6068,plain,
    ( u1_struct_0(sK5) = sK6
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK5),sK6,u1_struct_0(sK5)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5890,c_2914])).

cnf(c_6073,plain,
    ( u1_struct_0(sK5) = sK6
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6068,c_5890])).

cnf(c_5896,plain,
    ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_5882])).

cnf(c_2167,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
    | X0 != sK1(X2)
    | X1 != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_2368,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
    | X0 != sK1(X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_3527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | X0 != sK1(u1_struct_0(sK5))
    | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_4079,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | u1_struct_0(sK5) != sK1(u1_struct_0(sK5))
    | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3527])).

cnf(c_4080,plain,
    ( u1_struct_0(sK5) != sK1(u1_struct_0(sK5))
    | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5))
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4079])).

cnf(c_1501,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2403,plain,
    ( X0 != u1_struct_0(sK5)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_3169,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | k1_zfmisc_1(u1_struct_0(sK5)) = k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_4,plain,
    ( ~ v1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | X0 = sK1(X0) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_493,plain,
    ( X0 = sK1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_5])).

cnf(c_2512,plain,
    ( u1_struct_0(sK5) = sK1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_2128,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2134,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_267,plain,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_499,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | u1_struct_0(sK5) != X0
    | sK1(X0) != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_267])).

cnf(c_500,plain,
    ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
    | sK1(u1_struct_0(sK5)) != sK6 ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_1906,plain,
    ( sK1(u1_struct_0(sK5)) != sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1937,plain,
    ( u1_struct_0(sK5) != sK6
    | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1906,c_493])).

cnf(c_1508,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1520,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6073,c_5896,c_4080,c_3169,c_2512,c_2134,c_1937,c_1525,c_1520,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:23:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 24
% 3.04/0.99  conjectures                             2
% 3.04/0.99  EPR                                     2
% 3.04/0.99  Horn                                    16
% 3.04/0.99  unary                                   6
% 3.04/0.99  binary                                  4
% 3.04/0.99  lits                                    64
% 3.04/0.99  lits eq                                 10
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 2
% 3.04/0.99  fd_pseudo_cond                          3
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f2,axiom,(
% 3.04/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f21,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f2])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(flattening,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(nnf_transformation,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(flattening,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1)) & (r2_hidden(sK0(X0,X1,X2),X2) | r2_hidden(sK0(X0,X1,X2),X1)) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.04/0.99  
% 3.04/0.99  fof(f62,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK0(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,axiom,(
% 3.04/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f36,plain,(
% 3.04/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f55,plain,(
% 3.04/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(nnf_transformation,[],[f36])).
% 3.04/0.99  
% 3.04/0.99  fof(f85,plain,(
% 3.04/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f55])).
% 3.04/0.99  
% 3.04/0.99  fof(f13,conjecture,(
% 3.04/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f14,negated_conjecture,(
% 3.04/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.04/0.99    inference(negated_conjecture,[],[f13])).
% 3.04/0.99  
% 3.04/0.99  fof(f15,plain,(
% 3.04/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.04/0.99  
% 3.04/0.99  fof(f16,plain,(
% 3.04/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,plain,(
% 3.04/0.99    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f56,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f56])).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK6) | ~v1_subset_1(sK6,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK6) | v1_subset_1(sK6,u1_struct_0(X0))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK6,X0) & ~v1_xboole_0(sK6))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f58,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK5),X1) | ~v1_subset_1(X1,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),X1) | v1_subset_1(X1,u1_struct_0(sK5))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(X1,sK5) & ~v1_xboole_0(X1)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f60,plain,(
% 3.04/0.99    ((r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))) & (~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & v13_waybel_0(sK6,sK5) & ~v1_xboole_0(sK6)) & l1_orders_2(sK5) & v1_yellow_0(sK5) & v5_orders_2(sK5) & ~v2_struct_0(sK5)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f59,f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f94,plain,(
% 3.04/0.99    r2_hidden(k3_yellow_0(sK5),sK6) | ~v1_subset_1(sK6,u1_struct_0(sK5))),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f92,plain,(
% 3.04/0.99    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f10,axiom,(
% 3.04/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f18,plain,(
% 3.04/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f18])).
% 3.04/0.99  
% 3.04/0.99  fof(f77,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f33])).
% 3.04/0.99  
% 3.04/0.99  fof(f89,plain,(
% 3.04/0.99    l1_orders_2(sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f7,axiom,(
% 3.04/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f28,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f7])).
% 3.04/0.99  
% 3.04/0.99  fof(f29,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(flattening,[],[f28])).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f29])).
% 3.04/0.99  
% 3.04/0.99  fof(f46,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(flattening,[],[f45])).
% 3.04/0.99  
% 3.04/0.99  fof(f47,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(rectify,[],[f46])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f49,plain,(
% 3.04/0.99    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_lattice3(X0,X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 3.04/0.99  
% 3.04/0.99  fof(f71,plain,(
% 3.04/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f49])).
% 3.04/0.99  
% 3.04/0.99  fof(f95,plain,(
% 3.04/0.99    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f71])).
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f8])).
% 3.04/0.99  
% 3.04/0.99  fof(f75,plain,(
% 3.04/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f9,axiom,(
% 3.04/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f19,plain,(
% 3.04/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f76,plain,(
% 3.04/0.99    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f32])).
% 3.04/0.99  
% 3.04/0.99  fof(f88,plain,(
% 3.04/0.99    v1_yellow_0(sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f86,plain,(
% 3.04/0.99    ~v2_struct_0(sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f87,plain,(
% 3.04/0.99    v5_orders_2(sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f6,axiom,(
% 3.04/0.99    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f27,plain,(
% 3.04/0.99    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f6])).
% 3.04/0.99  
% 3.04/0.99  fof(f69,plain,(
% 3.04/0.99    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f34,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f35,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(flattening,[],[f34])).
% 3.04/0.99  
% 3.04/0.99  fof(f50,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(nnf_transformation,[],[f35])).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(rectify,[],[f50])).
% 3.04/0.99  
% 3.04/0.99  fof(f53,plain,(
% 3.04/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,X2,sK4(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f52,plain,(
% 3.04/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK3(X0,X1),X3) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK4(X0,X1),X1) & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f51,f53,f52])).
% 3.04/0.99  
% 3.04/0.99  fof(f78,plain,(
% 3.04/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f54])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f25,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f26,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.04/0.99    inference(flattening,[],[f25])).
% 3.04/0.99  
% 3.04/0.99  fof(f68,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f26])).
% 3.04/0.99  
% 3.04/0.99  fof(f91,plain,(
% 3.04/0.99    v13_waybel_0(sK6,sK5)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f4,axiom,(
% 3.04/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f23,plain,(
% 3.04/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.04/0.99    inference(ennf_transformation,[],[f4])).
% 3.04/0.99  
% 3.04/0.99  fof(f24,plain,(
% 3.04/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.04/0.99    inference(flattening,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f67,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f24])).
% 3.04/0.99  
% 3.04/0.99  fof(f90,plain,(
% 3.04/0.99    ~v1_xboole_0(sK6)),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f20,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f61,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f64,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK0(X0,X1,X2),X2) | ~r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f3,axiom,(
% 3.04/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ! [X0] : (~v1_subset_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f66,plain,(
% 3.04/0.99    ( ! [X0] : (~v1_subset_1(sK1(X0),X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f65,plain,(
% 3.04/0.99    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f93,plain,(
% 3.04/0.99    ~r2_hidden(k3_yellow_0(sK5),sK6) | v1_subset_1(sK6,u1_struct_0(sK5))),
% 3.04/0.99    inference(cnf_transformation,[],[f60])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.04/0.99      | m1_subset_1(sK0(X1,X0,X2),X1)
% 3.04/0.99      | X0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1912,plain,
% 3.04/0.99      ( X0 = X1
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.04/0.99      | m1_subset_1(sK0(X2,X0,X1),X2) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_23,plain,
% 3.04/0.99      ( v1_subset_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | X0 = X1 ),
% 3.04/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_25,negated_conjecture,
% 3.04/0.99      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_269,plain,
% 3.04/0.99      ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 3.04/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_511,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | X1 = X0
% 3.04/0.99      | u1_struct_0(sK5) != X1
% 3.04/0.99      | sK6 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_269]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_512,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | u1_struct_0(sK5) = sK6 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_514,plain,
% 3.04/0.99      ( r2_hidden(k3_yellow_0(sK5),sK6) | u1_struct_0(sK5) = sK6 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_512,c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1905,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = sK6
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_16,plain,
% 3.04/0.99      ( r2_lattice3(X0,k1_xboole_0,X1)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_30,negated_conjecture,
% 3.04/0.99      ( l1_orders_2(sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_774,plain,
% 3.04/0.99      ( r2_lattice3(X0,k1_xboole_0,X1)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.99      | sK5 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_775,plain,
% 3.04/0.99      ( r2_lattice3(sK5,k1_xboole_0,X0)
% 3.04/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_774]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_12,plain,
% 3.04/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.04/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.04/0.99      | ~ r1_yellow_0(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_14,plain,
% 3.04/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_210,plain,
% 3.04/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ r1_yellow_0(X0,X1)
% 3.04/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.04/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_12,c_14]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_211,plain,
% 3.04/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.04/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.04/0.99      | ~ r1_yellow_0(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_15,plain,
% 3.04/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ v5_orders_2(X0)
% 3.04/0.99      | ~ v1_yellow_0(X0)
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_31,negated_conjecture,
% 3.04/0.99      ( v1_yellow_0(sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_474,plain,
% 3.04/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.04/0.99      | v2_struct_0(X0)
% 3.04/0.99      | ~ v5_orders_2(X0)
% 3.04/0.99      | ~ l1_orders_2(X0)
% 3.04/0.99      | sK5 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_475,plain,
% 3.04/0.99      ( r1_yellow_0(sK5,k1_xboole_0)
% 3.04/0.99      | v2_struct_0(sK5)
% 3.04/0.99      | ~ v5_orders_2(sK5)
% 3.04/0.99      | ~ l1_orders_2(sK5) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_474]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,negated_conjecture,
% 3.04/0.99      ( ~ v2_struct_0(sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_32,negated_conjecture,
% 3.04/0.99      ( v5_orders_2(sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_69,plain,
% 3.04/0.99      ( r1_yellow_0(sK5,k1_xboole_0)
% 3.04/0.99      | v2_struct_0(sK5)
% 3.04/0.99      | ~ v5_orders_2(sK5)
% 3.04/0.99      | ~ v1_yellow_0(sK5)
% 3.04/0.99      | ~ l1_orders_2(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_477,plain,
% 3.04/0.99      ( r1_yellow_0(sK5,k1_xboole_0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_475,c_33,c_32,c_31,c_30,c_69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_549,plain,
% 3.04/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.04/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.04/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ l1_orders_2(X0)
% 3.04/0.99      | sK5 != X0
% 3.04/0.99      | k1_xboole_0 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_211,c_477]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_550,plain,
% 3.04/0.99      ( ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 3.04/0.99      | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 3.04/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.99      | ~ l1_orders_2(sK5) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_549]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_554,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.99      | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 3.04/0.99      | ~ r2_lattice3(sK5,k1_xboole_0,X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_550,c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_555,plain,
% 3.04/0.99      ( ~ r2_lattice3(sK5,k1_xboole_0,X0)
% 3.04/0.99      | r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 3.04/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_554]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_828,plain,
% 3.04/0.99      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0)
% 3.04/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.04/0.99      inference(backward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_775,c_555]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1896,plain,
% 3.04/0.99      ( r1_orders_2(sK5,k1_yellow_0(sK5,k1_xboole_0),X0) = iProver_top
% 3.04/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8,plain,
% 3.04/0.99      ( ~ l1_orders_2(X0)
% 3.04/0.99      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_795,plain,
% 3.04/0.99      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK5 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_796,plain,
% 3.04/0.99      ( k1_yellow_0(sK5,k1_xboole_0) = k3_yellow_0(sK5) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_795]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1942,plain,
% 3.04/0.99      ( r1_orders_2(sK5,k3_yellow_0(sK5),X0) = iProver_top
% 3.04/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1896,c_796]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1909,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,plain,
% 3.04/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.04/0.99      | ~ v13_waybel_0(X3,X0)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ r2_hidden(X1,X3)
% 3.04/0.99      | r2_hidden(X2,X3)
% 3.04/0.99      | ~ l1_orders_2(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_734,plain,
% 3.04/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.04/0.99      | ~ v13_waybel_0(X3,X0)
% 3.04/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.99      | ~ r2_hidden(X1,X3)
% 3.04/0.99      | r2_hidden(X2,X3)
% 3.04/0.99      | sK5 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_735,plain,
% 3.04/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ v13_waybel_0(X2,sK5)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ r2_hidden(X0,X2)
% 3.04/0.99      | r2_hidden(X1,X2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_734]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,plain,
% 3.04/0.99      ( m1_subset_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ r2_hidden(X0,X2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_751,plain,
% 3.04/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ v13_waybel_0(X2,sK5)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ r2_hidden(X0,X2)
% 3.04/0.99      | r2_hidden(X1,X2) ),
% 3.04/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_735,c_7]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1899,plain,
% 3.04/0.99      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 3.04/0.99      | v13_waybel_0(X2,sK5) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.04/0.99      | r2_hidden(X1,X2) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2876,plain,
% 3.04/0.99      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 3.04/0.99      | v13_waybel_0(sK6,sK5) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.04/0.99      | r2_hidden(X1,sK6) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1909,c_1899]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_28,negated_conjecture,
% 3.04/0.99      ( v13_waybel_0(sK6,sK5) ),
% 3.04/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_936,plain,
% 3.04/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ r2_hidden(X0,X2)
% 3.04/0.99      | r2_hidden(X1,X2)
% 3.04/0.99      | sK6 != X2
% 3.04/0.99      | sK5 != sK5 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_751]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_937,plain,
% 3.04/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ r2_hidden(X0,sK6)
% 3.04/0.99      | r2_hidden(X1,sK6) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_936]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_939,plain,
% 3.04/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ r2_hidden(X0,sK6)
% 3.04/0.99      | r2_hidden(X1,sK6) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_937,c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_940,plain,
% 3.04/0.99      ( ~ r1_orders_2(sK5,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.99      | ~ r2_hidden(X0,sK6)
% 3.04/0.99      | r2_hidden(X1,sK6) ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_939]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_941,plain,
% 3.04/0.99      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.04/0.99      | r2_hidden(X1,sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3084,plain,
% 3.04/0.99      ( r1_orders_2(sK5,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.04/0.99      | r2_hidden(X1,sK6) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2876,c_941]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3093,plain,
% 3.04/0.99      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) = iProver_top
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1942,c_3084]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3574,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = sK6
% 3.04/0.99      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1905,c_3093]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1504,plain,
% 3.04/0.99      ( X0 != X1 | k3_yellow_0(X0) = k3_yellow_0(X1) ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1516,plain,
% 3.04/0.99      ( k3_yellow_0(sK5) = k3_yellow_0(sK5) | sK5 != sK5 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1504]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1498,plain,( X0 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1525,plain,
% 3.04/0.99      ( sK5 = sK5 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1498]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_786,plain,
% 3.04/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK5 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_787,plain,
% 3.04/0.99      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_786]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1897,plain,
% 3.04/0.99      ( m1_subset_1(k1_yellow_0(sK5,X0),u1_struct_0(sK5)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2150,plain,
% 3.04/0.99      ( m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_796,c_1897]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2244,plain,
% 3.04/0.99      ( sK6 = sK6 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1498]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1499,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2224,plain,
% 3.04/0.99      ( u1_struct_0(sK5) != X0 | sK6 != X0 | sK6 = u1_struct_0(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1499]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2644,plain,
% 3.04/0.99      ( u1_struct_0(sK5) != sK6 | sK6 = u1_struct_0(sK5) | sK6 != sK6 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2224]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1502,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2698,plain,
% 3.04/0.99      ( m1_subset_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 3.04/0.99      | X1 != u1_struct_0(sK5)
% 3.04/0.99      | X0 != k3_yellow_0(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1502]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3026,plain,
% 3.04/0.99      ( m1_subset_1(X0,sK6)
% 3.04/0.99      | ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 3.04/0.99      | X0 != k3_yellow_0(sK5)
% 3.04/0.99      | sK6 != u1_struct_0(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2698]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4032,plain,
% 3.04/0.99      ( ~ m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5))
% 3.04/0.99      | m1_subset_1(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 3.04/0.99      | sK6 != u1_struct_0(sK5) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3026]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4034,plain,
% 3.04/0.99      ( k3_yellow_0(sK5) != k3_yellow_0(sK5)
% 3.04/0.99      | sK6 != u1_struct_0(sK5)
% 3.04/0.99      | m1_subset_1(k3_yellow_0(sK5),u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | m1_subset_1(k3_yellow_0(sK5),sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4032]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_29,negated_conjecture,
% 3.04/0.99      ( ~ v1_xboole_0(sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_459,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK6 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_460,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,sK6) | r2_hidden(X0,sK6) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5673,plain,
% 3.04/0.99      ( ~ m1_subset_1(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_460]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5674,plain,
% 3.04/0.99      ( m1_subset_1(k3_yellow_0(sK5),sK6) != iProver_top
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_5673]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5882,plain,
% 3.04/0.99      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_3574,c_1516,c_1525,c_2150,c_2244,c_2644,c_3093,c_4034,
% 3.04/0.99                 c_5674]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5890,plain,
% 3.04/0.99      ( X0 = X1
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(u1_struct_0(sK5),X1,X0),sK6) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1912,c_5882]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ r2_hidden(X2,X0)
% 3.04/0.99      | r2_hidden(X2,X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1915,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.04/0.99      | r2_hidden(X2,X0) != iProver_top
% 3.04/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2433,plain,
% 3.04/0.99      ( r2_hidden(X0,u1_struct_0(sK5)) = iProver_top
% 3.04/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1909,c_1915]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ r2_hidden(sK0(X1,X0,X2),X2)
% 3.04/0.99      | ~ r2_hidden(sK0(X1,X0,X2),X0)
% 3.04/0.99      | X0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1914,plain,
% 3.04/0.99      ( X0 = X1
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.04/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(X2,X0,X1),X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2914,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = X0
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X1)) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(X1,X0,u1_struct_0(sK5)),X0) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(X1,X0,u1_struct_0(sK5)),sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2433,c_1914]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6068,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = sK6
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | r2_hidden(sK0(u1_struct_0(sK5),sK6,u1_struct_0(sK5)),sK6) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_5890,c_2914]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6073,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = sK6
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.99      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.04/0.99      inference(forward_subsumption_resolution,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6068,c_5890]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5896,plain,
% 3.04/0.99      ( r2_hidden(k3_yellow_0(sK5),sK6) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2150,c_5882]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2167,plain,
% 3.04/0.99      ( m1_subset_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(sK1(X2),k1_zfmisc_1(X2))
% 3.04/0.99      | X0 != sK1(X2)
% 3.04/0.99      | X1 != k1_zfmisc_1(X2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1502]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2368,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | ~ m1_subset_1(sK1(X1),k1_zfmisc_1(X1))
% 3.04/0.99      | X0 != sK1(X1)
% 3.04/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2167]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3527,plain,
% 3.04/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | X0 != sK1(u1_struct_0(sK5))
% 3.04/0.99      | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2368]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4079,plain,
% 3.04/0.99      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.99      | u1_struct_0(sK5) != sK1(u1_struct_0(sK5))
% 3.04/0.99      | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_3527]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4080,plain,
% 3.04/0.99      ( u1_struct_0(sK5) != sK1(u1_struct_0(sK5))
% 3.04/0.99      | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5))
% 3.04/0.99      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.04/0.99      | m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4079]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1501,plain,
% 3.04/0.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2403,plain,
% 3.04/0.99      ( X0 != u1_struct_0(sK5)
% 3.04/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK5)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1501]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3169,plain,
% 3.04/0.99      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.04/0.99      | k1_zfmisc_1(u1_struct_0(sK5)) = k1_zfmisc_1(u1_struct_0(sK5)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_2403]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( ~ v1_subset_1(sK1(X0),X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_488,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.99      | X1 != X2
% 3.04/0.99      | X1 = X0
% 3.04/0.99      | sK1(X2) != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_489,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) | X0 = sK1(X0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_488]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_493,plain,
% 3.04/0.99      ( X0 = sK1(X0) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_489,c_5]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2512,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = sK1(u1_struct_0(sK5)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_493]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2128,plain,
% 3.04/0.99      ( m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2134,plain,
% 3.04/0.99      ( m1_subset_1(sK1(u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_26,negated_conjecture,
% 3.04/0.99      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.99      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 3.04/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_267,plain,
% 3.04/0.99      ( v1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.99      | ~ r2_hidden(k3_yellow_0(sK5),sK6) ),
% 3.04/0.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_499,plain,
% 3.04/0.99      ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | u1_struct_0(sK5) != X0
% 3.04/0.99      | sK1(X0) != sK6 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_267]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_500,plain,
% 3.04/0.99      ( ~ r2_hidden(k3_yellow_0(sK5),sK6)
% 3.04/0.99      | sK1(u1_struct_0(sK5)) != sK6 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_499]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1906,plain,
% 3.04/0.99      ( sK1(u1_struct_0(sK5)) != sK6
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1937,plain,
% 3.04/0.99      ( u1_struct_0(sK5) != sK6
% 3.04/0.99      | r2_hidden(k3_yellow_0(sK5),sK6) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1906,c_493]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1508,plain,
% 3.04/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.04/0.99      theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1520,plain,
% 3.04/0.99      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_40,plain,
% 3.04/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6073,c_5896,c_4080,c_3169,c_2512,c_2134,c_1937,c_1525,
% 3.04/0.99                 c_1520,c_40]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.012
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.011
% 3.04/0.99  total_time:                             0.199
% 3.04/0.99  num_of_symbols:                         55
% 3.04/0.99  num_of_terms:                           4831
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          0
% 3.04/0.99  num_of_split_atoms:                     0
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    27
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        0
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       135
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        55
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        4
% 3.04/0.99  pred_elim:                              8
% 3.04/0.99  pred_elim_cl:                           10
% 3.04/0.99  pred_elim_cycles:                       12
% 3.04/0.99  merged_defs:                            2
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          2
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.019
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                24
% 3.04/0.99  conjectures:                            2
% 3.04/0.99  epr:                                    2
% 3.04/0.99  horn:                                   16
% 3.04/0.99  ground:                                 6
% 3.04/0.99  unary:                                  6
% 3.04/0.99  binary:                                 4
% 3.04/0.99  lits:                                   64
% 3.04/0.99  lits_eq:                                10
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                2
% 3.04/0.99  fd_pseudo_cond:                         3
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      28
% 3.04/0.99  prop_fast_solver_calls:                 1220
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    1650
% 3.04/0.99  prop_preprocess_simplified:             5518
% 3.04/0.99  prop_fo_subsumed:                       22
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    421
% 3.04/0.99  inst_num_in_passive:                    90
% 3.04/0.99  inst_num_in_active:                     242
% 3.04/0.99  inst_num_in_unprocessed:                89
% 3.04/0.99  inst_num_of_loops:                      300
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          55
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      111
% 3.04/0.99  inst_num_of_non_proper_insts:           507
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       139
% 3.04/0.99  res_forward_subset_subsumed:            75
% 3.04/0.99  res_backward_subset_subsumed:           0
% 3.04/0.99  res_forward_subsumed:                   0
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     2
% 3.04/0.99  res_backward_subsumption_resolution:    4
% 3.04/0.99  res_clause_to_clause_subsumption:       893
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      44
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     121
% 3.04/0.99  sup_num_in_active:                      58
% 3.04/0.99  sup_num_in_passive:                     63
% 3.04/0.99  sup_num_of_loops:                       59
% 3.04/0.99  sup_fw_superposition:                   83
% 3.04/0.99  sup_bw_superposition:                   56
% 3.04/0.99  sup_immediate_simplified:               21
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    0
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 4
% 3.04/0.99  sim_bw_subset_subsumed:                 2
% 3.04/0.99  sim_fw_subsumed:                        11
% 3.04/0.99  sim_bw_subsumed:                        4
% 3.04/0.99  sim_fw_subsumption_res:                 5
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      8
% 3.04/0.99  sim_eq_tautology_del:                   11
% 3.04/0.99  sim_eq_res_simp:                        0
% 3.04/0.99  sim_fw_demodulated:                     3
% 3.04/0.99  sim_bw_demodulated:                     0
% 3.04/0.99  sim_light_normalised:                   2
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
