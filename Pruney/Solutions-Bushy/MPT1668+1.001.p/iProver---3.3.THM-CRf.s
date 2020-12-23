%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1668+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:08 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  253 (7778 expanded)
%              Number of clauses        :  164 (1323 expanded)
%              Number of leaves         :   19 (2076 expanded)
%              Depth                    :   32
%              Number of atoms          : 1286 (82093 expanded)
%              Number of equality atoms :  248 (11059 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   28 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v14_waybel_0(X1,X0)
            <=> ? [X2] :
                  ( k5_waybel_0(X0,X2) = X1
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v14_waybel_0(X1,X0)
          <~> ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X2] :
                ( k5_waybel_0(X0,X2) = X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X3] :
                ( k5_waybel_0(X0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( k5_waybel_0(X0,X3) = X1
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k5_waybel_0(X0,sK7) = X1
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(X0,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v14_waybel_0(X1,X0) )
          & ( ? [X3] :
                ( k5_waybel_0(X0,X3) = X1
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | v14_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ! [X2] :
              ( k5_waybel_0(X0,X2) != sK6
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v14_waybel_0(sK6,X0) )
        & ( ? [X3] :
              ( k5_waybel_0(X0,X3) = sK6
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | v14_waybel_0(sK6,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK6,X0)
        & v1_waybel_0(sK6,X0)
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( k5_waybel_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) )
            & ( ? [X3] :
                  ( k5_waybel_0(X0,X3) = X1
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | v14_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( k5_waybel_0(sK5,X2) != X1
                | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
            | ~ v14_waybel_0(X1,sK5) )
          & ( ? [X3] :
                ( k5_waybel_0(sK5,X3) = X1
                & m1_subset_1(X3,u1_struct_0(sK5)) )
            | v14_waybel_0(X1,sK5) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
          & v12_waybel_0(X1,sK5)
          & v1_waybel_0(X1,sK5)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ! [X2] :
          ( k5_waybel_0(sK5,X2) != sK6
          | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
      | ~ v14_waybel_0(sK6,sK5) )
    & ( ( k5_waybel_0(sK5,sK7) = sK6
        & m1_subset_1(sK7,u1_struct_0(sK5)) )
      | v14_waybel_0(sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & v12_waybel_0(sK6,sK5)
    & v1_waybel_0(sK6,sK5)
    & ~ v1_xboole_0(sK6)
    & l1_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f60,f59,f58])).

fof(f99,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | v14_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,
    ( k5_waybel_0(sK5,sK7) = sK6
    | v14_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v14_waybel_0(X1,X0)
          <=> ? [X2] :
                ( r2_lattice3(X0,X1,X2)
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X2] :
                  ( r2_lattice3(X0,X1,X2)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ? [X3] :
                  ( r2_lattice3(X0,X1,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_lattice3(X0,X1,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_waybel_0(X1,X0)
              | ! [X2] :
                  ( ~ r2_lattice3(X0,X1,X2)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ( r2_lattice3(X0,X1,sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ v14_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK2(X0,X1))
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    v1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    v12_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r1_orders_2(X0,sK1(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & r1_orders_2(X0,sK1(X0,X1),sK0(X0,X1))
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ v14_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    ! [X2] :
      ( k5_waybel_0(sK5,X2) != sK6
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ v14_waybel_0(sK6,sK5) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v14_waybel_0(X1,X0)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_31,negated_conjecture,
    ( v14_waybel_0(sK6,sK5)
    | m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3519,plain,
    ( v14_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v14_waybel_0(sK6,sK5)
    | k5_waybel_0(sK5,sK7) = sK6 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3520,plain,
    ( k5_waybel_0(sK5,sK7) = sK6
    | v14_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ v1_waybel_0(X1,X0)
    | ~ v14_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v12_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,negated_conjecture,
    ( v1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_554,plain,
    ( r2_lattice3(X0,X1,sK2(X0,X1))
    | ~ v14_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v12_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_555,plain,
    ( r2_lattice3(sK5,sK6,sK2(sK5,sK6))
    | ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | v1_xboole_0(sK6)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,negated_conjecture,
    ( v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_36,negated_conjecture,
    ( l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_33,negated_conjecture,
    ( v12_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_557,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | r2_lattice3(sK5,sK6,sK2(sK5,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_39,c_38,c_37,c_36,c_35,c_33,c_32])).

cnf(c_558,plain,
    ( r2_lattice3(sK5,sK6,sK2(sK5,sK6))
    | ~ v14_waybel_0(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_557])).

cnf(c_3516,plain,
    ( r2_lattice3(sK5,sK6,sK2(sK5,sK6)) = iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_3518,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3522,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4295,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3518,c_3522])).

cnf(c_19,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_922,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_923,plain,
    ( ~ r2_lattice3(sK5,X0,X1)
    | r1_orders_2(sK5,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,u1_struct_0(sK5))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_3506,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_4442,plain,
    ( r2_lattice3(sK5,X0,X1) != iProver_top
    | r1_orders_2(sK5,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4295,c_3506])).

cnf(c_5715,plain,
    ( r1_orders_2(sK5,X0,sK2(sK5,sK6)) = iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK2(sK5,sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_4442])).

cnf(c_1359,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,X2)
    | sK2(sK5,sK6) != X1
    | sK6 != X2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_923])).

cnf(c_1360,plain,
    ( r1_orders_2(sK5,X0,sK2(sK5,sK6))
    | ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_1359])).

cnf(c_12,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v14_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v12_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_592,plain,
    ( ~ v14_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v12_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_593,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v12_waybel_0(sK6,sK5)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | v1_xboole_0(sK6)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_592])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v14_waybel_0(sK6,sK5)
    | r1_orders_2(sK5,X0,sK2(sK5,sK6))
    | ~ r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_39,c_38,c_37,c_36,c_35,c_33,c_32,c_593])).

cnf(c_1365,plain,
    ( r1_orders_2(sK5,X0,sK2(sK5,sK6))
    | ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(renaming,[status(thm)],[c_1364])).

cnf(c_1366,plain,
    ( r1_orders_2(sK5,X0,sK2(sK5,sK6)) = iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_6295,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_orders_2(sK5,X0,sK2(sK5,sK6)) = iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5715,c_47,c_1366,c_3748])).

cnf(c_6296,plain,
    ( r1_orders_2(sK5,X0,sK2(sK5,sK6)) = iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6295])).

cnf(c_24,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_679,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_680,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r2_hidden(X0,k5_waybel_0(sK5,X1))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_684,plain,
    ( r2_hidden(X0,k5_waybel_0(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r1_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_36])).

cnf(c_685,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X0,k5_waybel_0(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_684])).

cnf(c_3508,plain,
    ( r1_orders_2(sK5,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k5_waybel_0(sK5,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k5_waybel_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_708,plain,
    ( m1_subset_1(k5_waybel_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_36])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(k5_waybel_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_708])).

cnf(c_3507,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(k5_waybel_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v12_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1073,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v12_waybel_0(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_36])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(sK5,X0),X0)
    | v12_waybel_0(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_1073])).

cnf(c_3497,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK1(sK5,X0),X0) != iProver_top
    | v12_waybel_0(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_4008,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK1(sK5,k5_waybel_0(sK5,X0)),k5_waybel_0(sK5,X0)) != iProver_top
    | v12_waybel_0(k5_waybel_0(sK5,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3507,c_3497])).

cnf(c_5710,plain,
    ( r1_orders_2(sK5,sK1(sK5,k5_waybel_0(sK5,X0)),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,k5_waybel_0(sK5,X0)),u1_struct_0(sK5)) != iProver_top
    | v12_waybel_0(k5_waybel_0(sK5,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_4008])).

cnf(c_6304,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK1(sK5,k5_waybel_0(sK5,sK2(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK1(sK5,k5_waybel_0(sK5,sK2(sK5,sK6))),sK6) != iProver_top
    | v12_waybel_0(k5_waybel_0(sK5,sK2(sK5,sK6)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6296,c_5710])).

cnf(c_46,plain,
    ( v12_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_595,plain,
    ( m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | ~ v14_waybel_0(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_39,c_38,c_37,c_36,c_35,c_33,c_32])).

cnf(c_596,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_597,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_11,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v14_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ v12_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_606,plain,
    ( ~ v14_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ v12_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | sK6 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_607,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK2(sK5,sK6),sK6)
    | ~ v12_waybel_0(sK6,sK5)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | v1_xboole_0(sK6)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_609,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | r2_hidden(sK2(sK5,sK6),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_39,c_38,c_37,c_36,c_35,c_33,c_32])).

cnf(c_611,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(sK2(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_29,negated_conjecture,
    ( ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | k5_waybel_0(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3596,plain,
    ( ~ v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | k5_waybel_0(sK5,sK2(sK5,sK6)) != sK6 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3597,plain,
    ( k5_waybel_0(sK5,sK2(sK5,sK6)) != sK6
    | v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3596])).

cnf(c_3599,plain,
    ( m1_subset_1(k5_waybel_0(sK5,sK2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_3600,plain,
    ( m1_subset_1(k5_waybel_0(sK5,sK2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3599])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3761,plain,
    ( ~ r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6)
    | ~ r1_tarski(sK6,k5_waybel_0(sK5,sK2(sK5,sK6)))
    | k5_waybel_0(sK5,sK2(sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3762,plain,
    ( k5_waybel_0(sK5,sK2(sK5,sK6)) = sK6
    | r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6) != iProver_top
    | r1_tarski(sK6,k5_waybel_0(sK5,sK2(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3761])).

cnf(c_14,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3905,plain,
    ( r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6)))
    | r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3909,plain,
    ( r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top
    | r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3905])).

cnf(c_13,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3904,plain,
    ( ~ r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK6)
    | r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3911,plain,
    ( r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK6) != iProver_top
    | r1_tarski(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3904])).

cnf(c_3586,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3811,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(k5_waybel_0(sK5,sK2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k5_waybel_0(sK5,sK2(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_4897,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK5,sK2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5))
    | ~ r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_3811])).

cnf(c_4898,plain,
    ( m1_subset_1(k5_waybel_0(sK5,sK2(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5)) = iProver_top
    | r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4897])).

cnf(c_8,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_988,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_36])).

cnf(c_989,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK5) ),
    inference(unflattening,[status(thm)],[c_988])).

cnf(c_1005,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_989,c_28])).

cnf(c_3687,plain,
    ( ~ r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,sK6)
    | r2_hidden(X0,sK6)
    | ~ v12_waybel_0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_3780,plain,
    ( ~ r1_orders_2(sK5,X0,sK2(sK5,sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | ~ v12_waybel_0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_3687])).

cnf(c_10060,plain,
    ( ~ r1_orders_2(sK5,sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK2(sK5,sK6))
    | ~ m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK6)
    | ~ r2_hidden(sK2(sK5,sK6),sK6)
    | ~ v12_waybel_0(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_3780])).

cnf(c_10061,plain,
    ( r1_orders_2(sK5,sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK2(sK5,sK6)) != iProver_top
    | m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK6) = iProver_top
    | r2_hidden(sK2(sK5,sK6),sK6) != iProver_top
    | v12_waybel_0(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10060])).

cnf(c_25,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_659,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,k5_waybel_0(X0,X2))
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_660,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k5_waybel_0(sK5,X1))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_662,plain,
    ( ~ r2_hidden(X0,k5_waybel_0(sK5,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_orders_2(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_36])).

cnf(c_663,plain,
    ( r1_orders_2(sK5,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k5_waybel_0(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_21570,plain,
    ( r1_orders_2(sK5,sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK2(sK5,sK6))
    | ~ m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5))
    | ~ r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_21571,plain,
    ( r1_orders_2(sK5,sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),sK2(sK5,sK6)) = iProver_top
    | m1_subset_1(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(k5_waybel_0(sK5,sK2(sK5,sK6)),sK6),k5_waybel_0(sK5,sK2(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21570])).

cnf(c_3526,plain,
    ( r2_hidden(sK3(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3527,plain,
    ( r2_hidden(sK3(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4217,plain,
    ( r1_orders_2(sK5,sK3(X0,k5_waybel_0(sK5,X1)),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK3(X0,k5_waybel_0(sK5,X1)),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK5,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3508,c_3527])).

cnf(c_6303,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK2(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),sK6) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6296,c_4217])).

cnf(c_25073,plain,
    ( m1_subset_1(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
    | v14_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),sK6) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6303,c_597])).

cnf(c_25074,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),sK6) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top ),
    inference(renaming,[status(thm)],[c_25073])).

cnf(c_25079,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | r2_hidden(sK3(X0,k5_waybel_0(sK5,sK2(sK5,sK6))),sK6) != iProver_top
    | r1_tarski(X0,k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4295,c_25074])).

cnf(c_25737,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top
    | r1_tarski(sK6,k5_waybel_0(sK5,sK2(sK5,sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_25079])).

cnf(c_26118,plain,
    ( v14_waybel_0(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6304,c_46,c_47,c_597,c_611,c_3597,c_3600,c_3762,c_3909,c_3911,c_4898,c_10061,c_21571,c_25737])).

cnf(c_26122,plain,
    ( k5_waybel_0(sK5,sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_3520,c_26118])).

cnf(c_26192,plain,
    ( r1_orders_2(sK5,X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_26122,c_3508])).

cnf(c_48,plain,
    ( v14_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28012,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X0,sK7) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26192,c_46,c_47,c_48,c_597,c_611,c_3597,c_3600,c_3762,c_3909,c_3911,c_4898,c_10061,c_21571,c_25737])).

cnf(c_28013,plain,
    ( r1_orders_2(sK5,X0,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_28012])).

cnf(c_28019,plain,
    ( r1_orders_2(sK5,sK7,sK7) != iProver_top
    | v14_waybel_0(sK6,sK5) = iProver_top
    | r2_hidden(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3519,c_28013])).

cnf(c_18,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_943,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_944,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_3505,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,X0,X1),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_17,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_958,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK4(X0,X1,X2),X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_36])).

cnf(c_959,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(sK4(sK5,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_3504,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK4(sK5,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_3509,plain,
    ( r1_orders_2(sK5,X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,k5_waybel_0(sK5,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_4705,plain,
    ( r2_lattice3(sK5,k5_waybel_0(sK5,X0),X1) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k5_waybel_0(sK5,X0),X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK4(sK5,k5_waybel_0(sK5,X0),X1),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3504,c_3509])).

cnf(c_8487,plain,
    ( r2_lattice3(sK5,k5_waybel_0(sK5,X0),X1) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,k5_waybel_0(sK5,X0),X1),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3505,c_4705])).

cnf(c_16,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_973,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_974,plain,
    ( r2_lattice3(sK5,X0,X1)
    | ~ r1_orders_2(sK5,sK4(sK5,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_3503,plain,
    ( r2_lattice3(sK5,X0,X1) = iProver_top
    | r1_orders_2(sK5,sK4(sK5,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_9194,plain,
    ( r2_lattice3(sK5,k5_waybel_0(sK5,X0),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8487,c_3503])).

cnf(c_26160,plain,
    ( r2_lattice3(sK5,sK6,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26122,c_9194])).

cnf(c_26594,plain,
    ( r2_lattice3(sK5,sK6,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26160,c_46,c_47,c_48,c_597,c_611,c_3597,c_3600,c_3762,c_3909,c_3911,c_4898,c_10061,c_21571,c_25737])).

cnf(c_9,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ v1_waybel_0(X1,X0)
    | v14_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v12_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_568,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | v14_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v12_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_569,plain,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6)
    | ~ v12_waybel_0(sK6,sK5)
    | v2_struct_0(sK5)
    | ~ v3_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | v1_xboole_0(sK6)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v14_waybel_0(sK6,sK5)
    | ~ r2_lattice3(sK5,sK6,X0)
    | ~ r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_39,c_38,c_37,c_36,c_35,c_33,c_32])).

cnf(c_574,plain,
    ( ~ r2_lattice3(sK5,sK6,X0)
    | v14_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X0,sK6) ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_3515,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | v14_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_575,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | v14_waybel_0(sK6,sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_3747,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_3586])).

cnf(c_3748,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3747])).

cnf(c_4105,plain,
    ( v14_waybel_0(sK6,sK5) = iProver_top
    | r2_lattice3(sK5,sK6,X0) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3515,c_47,c_575,c_3748])).

cnf(c_4106,plain,
    ( r2_lattice3(sK5,sK6,X0) != iProver_top
    | v14_waybel_0(sK6,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4105])).

cnf(c_26598,plain,
    ( v14_waybel_0(sK6,sK5) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_26594,c_4106])).

cnf(c_22,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_523,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ v3_orders_2(X0)
    | ~ v3_orders_2(X4)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X4)
    | X3 != X2
    | X3 != X1
    | X4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_23])).

cnf(c_524,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_634,plain,
    ( r1_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_524,c_38])).

cnf(c_635,plain,
    ( r1_orders_2(sK5,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( r1_orders_2(sK5,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_39,c_36])).

cnf(c_640,plain,
    ( r1_orders_2(sK5,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_2746,plain,
    ( r1_orders_2(sK5,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_640])).

cnf(c_3511,plain,
    ( r1_orders_2(sK5,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_2747,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_640])).

cnf(c_2745,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_640])).

cnf(c_2874,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_orders_2(sK5,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_2747,c_2745])).

cnf(c_2875,plain,
    ( r1_orders_2(sK5,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(renaming,[status(thm)],[c_2874])).

cnf(c_2876,plain,
    ( r1_orders_2(sK5,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2875])).

cnf(c_4016,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | r1_orders_2(sK5,X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3511,c_2876])).

cnf(c_4017,plain,
    ( r1_orders_2(sK5,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4016])).

cnf(c_4020,plain,
    ( r1_orders_2(sK5,sK7,sK7) = iProver_top
    | v14_waybel_0(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3519,c_4017])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28019,c_26598,c_26118,c_4020])).


%------------------------------------------------------------------------------
