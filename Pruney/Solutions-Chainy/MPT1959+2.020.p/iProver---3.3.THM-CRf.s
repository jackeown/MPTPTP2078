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
% DateTime   : Thu Dec  3 12:28:28 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  227 (3845 expanded)
%              Number of clauses        :  138 ( 899 expanded)
%              Number of leaves         :   25 ( 737 expanded)
%              Depth                    :   32
%              Number of atoms          :  968 (31306 expanded)
%              Number of equality atoms :  233 (1237 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(pure_predicate_removal,[],[f14])).

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
    inference(ennf_transformation,[],[f18])).

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
    inference(nnf_transformation,[],[f38])).

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
    inference(flattening,[],[f57])).

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f58,f60,f59])).

fof(f95,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
        & r2_lattice3(X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f49])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f43])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(rectify,[],[f51])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f61])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7)
    | ~ v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f103,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f99,plain,
    ( ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | v1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11,plain,
    ( ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1089,plain,
    ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_1090,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(unflattening,[status(thm)],[c_1089])).

cnf(c_19,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_12,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_12])).

cnf(c_239,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_37,negated_conjecture,
    ( v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_638,plain,
    ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_37])).

cnf(c_639,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
    | ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_643,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r1_yellow_0(sK6,X0)
    | ~ r2_lattice3(sK6,X0,X1)
    | r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_639,c_35])).

cnf(c_644,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
    | ~ r2_lattice3(sK6,X0,X1)
    | ~ r1_yellow_0(sK6,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_643])).

cnf(c_3332,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
    | r2_lattice3(sK6,X0,X1) != iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_3958,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3332])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_40,plain,
    ( v5_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_yellow_0(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( v1_yellow_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_21,plain,
    ( r1_yellow_0(X0,k1_xboole_0)
    | v2_struct_0(X0)
    | ~ v1_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_70,plain,
    ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_yellow_0(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_72,plain,
    ( r1_yellow_0(sK6,k1_xboole_0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v1_yellow_0(sK6) != iProver_top
    | v5_orders_2(sK6) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_4085,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3958,c_39,c_40,c_41,c_42,c_72])).

cnf(c_4086,plain,
    ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4085])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0),X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3341,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3338,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1040,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v13_waybel_0(X3,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_1041,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1057,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1041,c_6])).

cnf(c_3324,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_5273,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3338,c_3324])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( v13_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1268,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK7 != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_1057])).

cnf(c_1269,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_1268])).

cnf(c_1270,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_5394,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5273,c_45,c_1270])).

cnf(c_5402,plain,
    ( u1_struct_0(sK6) = X0
    | r1_orders_2(sK6,X1,sK1(u1_struct_0(sK6),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_5394])).

cnf(c_8726,plain,
    ( u1_struct_0(sK6) = X0
    | r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4086,c_5402])).

cnf(c_2742,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_2757,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2742])).

cnf(c_2733,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2766,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2733])).

cnf(c_3848,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6))
    | X0 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3854,plain,
    ( X0 = u1_struct_0(sK6)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3848])).

cnf(c_2734,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4327,plain,
    ( X0 != X1
    | u1_struct_0(sK6) != X1
    | u1_struct_0(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_5992,plain,
    ( X0 != u1_struct_0(sK6)
    | u1_struct_0(sK6) = X0
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_8,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1130,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_35])).

cnf(c_1131,plain,
    ( r2_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK2(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1130])).

cnf(c_3319,plain,
    ( r2_lattice3(sK6,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_20,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_231,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_12])).

cnf(c_232,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_662,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_37])).

cnf(c_663,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0))
    | ~ r1_yellow_0(sK6,X0)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_667,plain,
    ( ~ r1_yellow_0(sK6,X0)
    | r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_35])).

cnf(c_668,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0))
    | ~ r1_yellow_0(sK6,X0) ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_3331,plain,
    ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) = iProver_top
    | r1_yellow_0(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_3725,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3331])).

cnf(c_3893,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3725,c_39,c_40,c_41,c_42,c_72])).

cnf(c_1080,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_1081,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_1080])).

cnf(c_3322,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_3684,plain,
    ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3322])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1094,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_1095,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ r2_lattice3(sK6,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1094])).

cnf(c_3321,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r2_lattice3(sK6,X2,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1095])).

cnf(c_4304,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3684,c_3321])).

cnf(c_6601,plain,
    ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3893,c_4304])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_566,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_567,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_568,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_6616,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6601,c_568])).

cnf(c_6622,plain,
    ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_6616])).

cnf(c_6880,plain,
    ( u1_struct_0(sK6) = X0
    | r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3341,c_6622])).

cnf(c_5405,plain,
    ( r1_orders_2(sK6,X0,k1_yellow_0(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X1),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_5394])).

cnf(c_6389,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4086,c_5405])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_43,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( v13_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_101,plain,
    ( ~ l1_orders_2(sK6)
    | k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_28,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_311,plain,
    ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | X1 = X0
    | u1_struct_0(sK6) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_311])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) = sK7 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_606,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1082,plain,
    ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_3782,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2733])).

cnf(c_3620,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ r2_lattice3(sK6,k1_xboole_0,X0)
    | ~ r1_yellow_0(sK6,k1_xboole_0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_3831,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0))
    | ~ r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0))
    | ~ r1_yellow_0(sK6,k1_xboole_0)
    | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_3620])).

cnf(c_3836,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0)) = iProver_top
    | r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) != iProver_top
    | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3831])).

cnf(c_3732,plain,
    ( u1_struct_0(sK6) != X0
    | sK7 != X0
    | sK7 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_5215,plain,
    ( u1_struct_0(sK6) != sK7
    | sK7 = u1_struct_0(sK6)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3732])).

cnf(c_2738,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4488,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != k3_yellow_0(sK6)
    | X1 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2738])).

cnf(c_5039,plain,
    ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | X0 != u1_struct_0(sK6)
    | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4488])).

cnf(c_6076,plain,
    ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7)
    | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
    | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5039])).

cnf(c_6078,plain,
    ( k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
    | sK7 != u1_struct_0(sK6)
    | m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7) = iProver_top
    | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6076])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3691,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6077,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7)
    | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_3691])).

cnf(c_6080,plain,
    ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6077])).

cnf(c_3673,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7)
    | r2_hidden(X1,sK7) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_6061,plain,
    ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,sK7)
    | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
    inference(instantiation,[status(thm)],[c_3673])).

cnf(c_6631,plain,
    ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0))
    | ~ v13_waybel_0(sK7,sK6)
    | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(k1_yellow_0(sK6,X0),sK7)
    | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
    inference(instantiation,[status(thm)],[c_6061])).

cnf(c_6632,plain,
    ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0)) != iProver_top
    | v13_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
    | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6631])).

cnf(c_6884,plain,
    ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_6622])).

cnf(c_7442,plain,
    ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6389,c_39,c_40,c_41,c_35,c_42,c_43,c_44,c_45,c_72,c_101,c_606,c_1082,c_3684,c_3782,c_3836,c_5215,c_6078,c_6080,c_6632,c_6884])).

cnf(c_7449,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_7442])).

cnf(c_13065,plain,
    ( r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8726,c_2757,c_2766,c_3854,c_5992,c_6880,c_7449])).

cnf(c_13066,plain,
    ( u1_struct_0(sK6) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_13065])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3342,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK1(X1,X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13075,plain,
    ( u1_struct_0(sK6) = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13066,c_3342])).

cnf(c_13288,plain,
    ( u1_struct_0(sK6) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13075,c_45])).

cnf(c_29,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_31,negated_conjecture,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_309,plain,
    ( v1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | u1_struct_0(sK6) != X0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_309])).

cnf(c_619,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k3_yellow_0(sK6),sK7)
    | sK7 != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_3333,plain,
    ( sK7 != u1_struct_0(sK6)
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_13347,plain,
    ( sK7 != sK7
    | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13288,c_3333])).

cnf(c_13535,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top
    | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13347])).

cnf(c_13374,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13288,c_3338])).

cnf(c_13538,plain,
    ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13535,c_13374])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13538,c_7449])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.94/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.98  
% 3.94/0.98  ------  iProver source info
% 3.94/0.98  
% 3.94/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.98  git: non_committed_changes: false
% 3.94/0.98  git: last_make_outside_of_git: false
% 3.94/0.98  
% 3.94/0.98  ------ 
% 3.94/0.98  
% 3.94/0.98  ------ Input Options
% 3.94/0.98  
% 3.94/0.98  --out_options                           all
% 3.94/0.98  --tptp_safe_out                         true
% 3.94/0.98  --problem_path                          ""
% 3.94/0.98  --include_path                          ""
% 3.94/0.98  --clausifier                            res/vclausify_rel
% 3.94/0.98  --clausifier_options                    --mode clausify
% 3.94/0.98  --stdin                                 false
% 3.94/0.98  --stats_out                             all
% 3.94/0.98  
% 3.94/0.98  ------ General Options
% 3.94/0.98  
% 3.94/0.98  --fof                                   false
% 3.94/0.98  --time_out_real                         305.
% 3.94/0.98  --time_out_virtual                      -1.
% 3.94/0.98  --symbol_type_check                     false
% 3.94/0.98  --clausify_out                          false
% 3.94/0.98  --sig_cnt_out                           false
% 3.94/0.98  --trig_cnt_out                          false
% 3.94/0.98  --trig_cnt_out_tolerance                1.
% 3.94/0.98  --trig_cnt_out_sk_spl                   false
% 3.94/0.98  --abstr_cl_out                          false
% 3.94/0.98  
% 3.94/0.98  ------ Global Options
% 3.94/0.98  
% 3.94/0.98  --schedule                              default
% 3.94/0.98  --add_important_lit                     false
% 3.94/0.98  --prop_solver_per_cl                    1000
% 3.94/0.98  --min_unsat_core                        false
% 3.94/0.98  --soft_assumptions                      false
% 3.94/0.98  --soft_lemma_size                       3
% 3.94/0.98  --prop_impl_unit_size                   0
% 3.94/0.98  --prop_impl_unit                        []
% 3.94/0.98  --share_sel_clauses                     true
% 3.94/0.98  --reset_solvers                         false
% 3.94/0.98  --bc_imp_inh                            [conj_cone]
% 3.94/0.98  --conj_cone_tolerance                   3.
% 3.94/0.98  --extra_neg_conj                        none
% 3.94/0.98  --large_theory_mode                     true
% 3.94/0.98  --prolific_symb_bound                   200
% 3.94/0.98  --lt_threshold                          2000
% 3.94/0.98  --clause_weak_htbl                      true
% 3.94/0.98  --gc_record_bc_elim                     false
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing Options
% 3.94/0.98  
% 3.94/0.98  --preprocessing_flag                    true
% 3.94/0.98  --time_out_prep_mult                    0.1
% 3.94/0.98  --splitting_mode                        input
% 3.94/0.98  --splitting_grd                         true
% 3.94/0.98  --splitting_cvd                         false
% 3.94/0.98  --splitting_cvd_svl                     false
% 3.94/0.98  --splitting_nvd                         32
% 3.94/0.98  --sub_typing                            true
% 3.94/0.98  --prep_gs_sim                           true
% 3.94/0.98  --prep_unflatten                        true
% 3.94/0.98  --prep_res_sim                          true
% 3.94/0.98  --prep_upred                            true
% 3.94/0.98  --prep_sem_filter                       exhaustive
% 3.94/0.98  --prep_sem_filter_out                   false
% 3.94/0.98  --pred_elim                             true
% 3.94/0.98  --res_sim_input                         true
% 3.94/0.98  --eq_ax_congr_red                       true
% 3.94/0.98  --pure_diseq_elim                       true
% 3.94/0.98  --brand_transform                       false
% 3.94/0.98  --non_eq_to_eq                          false
% 3.94/0.98  --prep_def_merge                        true
% 3.94/0.98  --prep_def_merge_prop_impl              false
% 3.94/0.98  --prep_def_merge_mbd                    true
% 3.94/0.98  --prep_def_merge_tr_red                 false
% 3.94/0.98  --prep_def_merge_tr_cl                  false
% 3.94/0.98  --smt_preprocessing                     true
% 3.94/0.98  --smt_ac_axioms                         fast
% 3.94/0.98  --preprocessed_out                      false
% 3.94/0.98  --preprocessed_stats                    false
% 3.94/0.98  
% 3.94/0.98  ------ Abstraction refinement Options
% 3.94/0.98  
% 3.94/0.98  --abstr_ref                             []
% 3.94/0.98  --abstr_ref_prep                        false
% 3.94/0.98  --abstr_ref_until_sat                   false
% 3.94/0.98  --abstr_ref_sig_restrict                funpre
% 3.94/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.98  --abstr_ref_under                       []
% 3.94/0.98  
% 3.94/0.98  ------ SAT Options
% 3.94/0.98  
% 3.94/0.98  --sat_mode                              false
% 3.94/0.98  --sat_fm_restart_options                ""
% 3.94/0.98  --sat_gr_def                            false
% 3.94/0.98  --sat_epr_types                         true
% 3.94/0.98  --sat_non_cyclic_types                  false
% 3.94/0.98  --sat_finite_models                     false
% 3.94/0.98  --sat_fm_lemmas                         false
% 3.94/0.98  --sat_fm_prep                           false
% 3.94/0.98  --sat_fm_uc_incr                        true
% 3.94/0.98  --sat_out_model                         small
% 3.94/0.98  --sat_out_clauses                       false
% 3.94/0.98  
% 3.94/0.98  ------ QBF Options
% 3.94/0.98  
% 3.94/0.98  --qbf_mode                              false
% 3.94/0.98  --qbf_elim_univ                         false
% 3.94/0.98  --qbf_dom_inst                          none
% 3.94/0.98  --qbf_dom_pre_inst                      false
% 3.94/0.98  --qbf_sk_in                             false
% 3.94/0.98  --qbf_pred_elim                         true
% 3.94/0.98  --qbf_split                             512
% 3.94/0.98  
% 3.94/0.98  ------ BMC1 Options
% 3.94/0.98  
% 3.94/0.98  --bmc1_incremental                      false
% 3.94/0.98  --bmc1_axioms                           reachable_all
% 3.94/0.98  --bmc1_min_bound                        0
% 3.94/0.98  --bmc1_max_bound                        -1
% 3.94/0.98  --bmc1_max_bound_default                -1
% 3.94/0.98  --bmc1_symbol_reachability              true
% 3.94/0.98  --bmc1_property_lemmas                  false
% 3.94/0.98  --bmc1_k_induction                      false
% 3.94/0.98  --bmc1_non_equiv_states                 false
% 3.94/0.98  --bmc1_deadlock                         false
% 3.94/0.98  --bmc1_ucm                              false
% 3.94/0.98  --bmc1_add_unsat_core                   none
% 3.94/0.98  --bmc1_unsat_core_children              false
% 3.94/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.98  --bmc1_out_stat                         full
% 3.94/0.98  --bmc1_ground_init                      false
% 3.94/0.98  --bmc1_pre_inst_next_state              false
% 3.94/0.98  --bmc1_pre_inst_state                   false
% 3.94/0.98  --bmc1_pre_inst_reach_state             false
% 3.94/0.98  --bmc1_out_unsat_core                   false
% 3.94/0.98  --bmc1_aig_witness_out                  false
% 3.94/0.98  --bmc1_verbose                          false
% 3.94/0.98  --bmc1_dump_clauses_tptp                false
% 3.94/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.98  --bmc1_dump_file                        -
% 3.94/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.98  --bmc1_ucm_extend_mode                  1
% 3.94/0.98  --bmc1_ucm_init_mode                    2
% 3.94/0.98  --bmc1_ucm_cone_mode                    none
% 3.94/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.98  --bmc1_ucm_relax_model                  4
% 3.94/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.98  --bmc1_ucm_layered_model                none
% 3.94/0.98  --bmc1_ucm_max_lemma_size               10
% 3.94/0.98  
% 3.94/0.98  ------ AIG Options
% 3.94/0.98  
% 3.94/0.98  --aig_mode                              false
% 3.94/0.98  
% 3.94/0.98  ------ Instantiation Options
% 3.94/0.98  
% 3.94/0.98  --instantiation_flag                    true
% 3.94/0.98  --inst_sos_flag                         false
% 3.94/0.98  --inst_sos_phase                        true
% 3.94/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel_side                     num_symb
% 3.94/0.98  --inst_solver_per_active                1400
% 3.94/0.98  --inst_solver_calls_frac                1.
% 3.94/0.98  --inst_passive_queue_type               priority_queues
% 3.94/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.98  --inst_passive_queues_freq              [25;2]
% 3.94/0.98  --inst_dismatching                      true
% 3.94/0.98  --inst_eager_unprocessed_to_passive     true
% 3.94/0.98  --inst_prop_sim_given                   true
% 3.94/0.98  --inst_prop_sim_new                     false
% 3.94/0.98  --inst_subs_new                         false
% 3.94/0.98  --inst_eq_res_simp                      false
% 3.94/0.98  --inst_subs_given                       false
% 3.94/0.98  --inst_orphan_elimination               true
% 3.94/0.98  --inst_learning_loop_flag               true
% 3.94/0.98  --inst_learning_start                   3000
% 3.94/0.98  --inst_learning_factor                  2
% 3.94/0.98  --inst_start_prop_sim_after_learn       3
% 3.94/0.98  --inst_sel_renew                        solver
% 3.94/0.98  --inst_lit_activity_flag                true
% 3.94/0.98  --inst_restr_to_given                   false
% 3.94/0.98  --inst_activity_threshold               500
% 3.94/0.98  --inst_out_proof                        true
% 3.94/0.98  
% 3.94/0.98  ------ Resolution Options
% 3.94/0.98  
% 3.94/0.98  --resolution_flag                       true
% 3.94/0.98  --res_lit_sel                           adaptive
% 3.94/0.98  --res_lit_sel_side                      none
% 3.94/0.98  --res_ordering                          kbo
% 3.94/0.98  --res_to_prop_solver                    active
% 3.94/0.98  --res_prop_simpl_new                    false
% 3.94/0.98  --res_prop_simpl_given                  true
% 3.94/0.98  --res_passive_queue_type                priority_queues
% 3.94/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.98  --res_passive_queues_freq               [15;5]
% 3.94/0.98  --res_forward_subs                      full
% 3.94/0.98  --res_backward_subs                     full
% 3.94/0.98  --res_forward_subs_resolution           true
% 3.94/0.98  --res_backward_subs_resolution          true
% 3.94/0.98  --res_orphan_elimination                true
% 3.94/0.98  --res_time_limit                        2.
% 3.94/0.98  --res_out_proof                         true
% 3.94/0.98  
% 3.94/0.98  ------ Superposition Options
% 3.94/0.98  
% 3.94/0.98  --superposition_flag                    true
% 3.94/0.98  --sup_passive_queue_type                priority_queues
% 3.94/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.98  --demod_completeness_check              fast
% 3.94/0.98  --demod_use_ground                      true
% 3.94/0.98  --sup_to_prop_solver                    passive
% 3.94/0.98  --sup_prop_simpl_new                    true
% 3.94/0.98  --sup_prop_simpl_given                  true
% 3.94/0.98  --sup_fun_splitting                     false
% 3.94/0.98  --sup_smt_interval                      50000
% 3.94/0.98  
% 3.94/0.98  ------ Superposition Simplification Setup
% 3.94/0.98  
% 3.94/0.98  --sup_indices_passive                   []
% 3.94/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_full_bw                           [BwDemod]
% 3.94/0.98  --sup_immed_triv                        [TrivRules]
% 3.94/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_immed_bw_main                     []
% 3.94/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.98  
% 3.94/0.98  ------ Combination Options
% 3.94/0.98  
% 3.94/0.98  --comb_res_mult                         3
% 3.94/0.98  --comb_sup_mult                         2
% 3.94/0.98  --comb_inst_mult                        10
% 3.94/0.98  
% 3.94/0.98  ------ Debug Options
% 3.94/0.98  
% 3.94/0.98  --dbg_backtrace                         false
% 3.94/0.98  --dbg_dump_prop_clauses                 false
% 3.94/0.98  --dbg_dump_prop_clauses_file            -
% 3.94/0.98  --dbg_out_stat                          false
% 3.94/0.98  ------ Parsing...
% 3.94/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.98  ------ Proving...
% 3.94/0.98  ------ Problem Properties 
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  clauses                                 33
% 3.94/0.98  conjectures                             3
% 3.94/0.98  EPR                                     6
% 3.94/0.98  Horn                                    19
% 3.94/0.98  unary                                   7
% 3.94/0.98  binary                                  4
% 3.94/0.98  lits                                    93
% 3.94/0.98  lits eq                                 8
% 3.94/0.98  fd_pure                                 0
% 3.94/0.98  fd_pseudo                               0
% 3.94/0.98  fd_cond                                 0
% 3.94/0.98  fd_pseudo_cond                          5
% 3.94/0.98  AC symbols                              0
% 3.94/0.98  
% 3.94/0.98  ------ Schedule dynamic 5 is on 
% 3.94/0.98  
% 3.94/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  ------ 
% 3.94/0.98  Current options:
% 3.94/0.98  ------ 
% 3.94/0.98  
% 3.94/0.98  ------ Input Options
% 3.94/0.98  
% 3.94/0.98  --out_options                           all
% 3.94/0.98  --tptp_safe_out                         true
% 3.94/0.98  --problem_path                          ""
% 3.94/0.98  --include_path                          ""
% 3.94/0.98  --clausifier                            res/vclausify_rel
% 3.94/0.98  --clausifier_options                    --mode clausify
% 3.94/0.98  --stdin                                 false
% 3.94/0.98  --stats_out                             all
% 3.94/0.98  
% 3.94/0.98  ------ General Options
% 3.94/0.98  
% 3.94/0.98  --fof                                   false
% 3.94/0.98  --time_out_real                         305.
% 3.94/0.98  --time_out_virtual                      -1.
% 3.94/0.98  --symbol_type_check                     false
% 3.94/0.98  --clausify_out                          false
% 3.94/0.98  --sig_cnt_out                           false
% 3.94/0.98  --trig_cnt_out                          false
% 3.94/0.98  --trig_cnt_out_tolerance                1.
% 3.94/0.98  --trig_cnt_out_sk_spl                   false
% 3.94/0.98  --abstr_cl_out                          false
% 3.94/0.98  
% 3.94/0.98  ------ Global Options
% 3.94/0.98  
% 3.94/0.98  --schedule                              default
% 3.94/0.98  --add_important_lit                     false
% 3.94/0.98  --prop_solver_per_cl                    1000
% 3.94/0.98  --min_unsat_core                        false
% 3.94/0.98  --soft_assumptions                      false
% 3.94/0.98  --soft_lemma_size                       3
% 3.94/0.98  --prop_impl_unit_size                   0
% 3.94/0.98  --prop_impl_unit                        []
% 3.94/0.98  --share_sel_clauses                     true
% 3.94/0.98  --reset_solvers                         false
% 3.94/0.98  --bc_imp_inh                            [conj_cone]
% 3.94/0.98  --conj_cone_tolerance                   3.
% 3.94/0.98  --extra_neg_conj                        none
% 3.94/0.98  --large_theory_mode                     true
% 3.94/0.98  --prolific_symb_bound                   200
% 3.94/0.98  --lt_threshold                          2000
% 3.94/0.98  --clause_weak_htbl                      true
% 3.94/0.98  --gc_record_bc_elim                     false
% 3.94/0.98  
% 3.94/0.98  ------ Preprocessing Options
% 3.94/0.98  
% 3.94/0.98  --preprocessing_flag                    true
% 3.94/0.98  --time_out_prep_mult                    0.1
% 3.94/0.98  --splitting_mode                        input
% 3.94/0.98  --splitting_grd                         true
% 3.94/0.98  --splitting_cvd                         false
% 3.94/0.98  --splitting_cvd_svl                     false
% 3.94/0.98  --splitting_nvd                         32
% 3.94/0.98  --sub_typing                            true
% 3.94/0.98  --prep_gs_sim                           true
% 3.94/0.98  --prep_unflatten                        true
% 3.94/0.98  --prep_res_sim                          true
% 3.94/0.98  --prep_upred                            true
% 3.94/0.98  --prep_sem_filter                       exhaustive
% 3.94/0.98  --prep_sem_filter_out                   false
% 3.94/0.98  --pred_elim                             true
% 3.94/0.98  --res_sim_input                         true
% 3.94/0.98  --eq_ax_congr_red                       true
% 3.94/0.98  --pure_diseq_elim                       true
% 3.94/0.98  --brand_transform                       false
% 3.94/0.98  --non_eq_to_eq                          false
% 3.94/0.98  --prep_def_merge                        true
% 3.94/0.98  --prep_def_merge_prop_impl              false
% 3.94/0.98  --prep_def_merge_mbd                    true
% 3.94/0.98  --prep_def_merge_tr_red                 false
% 3.94/0.98  --prep_def_merge_tr_cl                  false
% 3.94/0.98  --smt_preprocessing                     true
% 3.94/0.98  --smt_ac_axioms                         fast
% 3.94/0.98  --preprocessed_out                      false
% 3.94/0.98  --preprocessed_stats                    false
% 3.94/0.98  
% 3.94/0.98  ------ Abstraction refinement Options
% 3.94/0.98  
% 3.94/0.98  --abstr_ref                             []
% 3.94/0.98  --abstr_ref_prep                        false
% 3.94/0.98  --abstr_ref_until_sat                   false
% 3.94/0.98  --abstr_ref_sig_restrict                funpre
% 3.94/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.98  --abstr_ref_under                       []
% 3.94/0.98  
% 3.94/0.98  ------ SAT Options
% 3.94/0.98  
% 3.94/0.98  --sat_mode                              false
% 3.94/0.98  --sat_fm_restart_options                ""
% 3.94/0.98  --sat_gr_def                            false
% 3.94/0.98  --sat_epr_types                         true
% 3.94/0.98  --sat_non_cyclic_types                  false
% 3.94/0.98  --sat_finite_models                     false
% 3.94/0.98  --sat_fm_lemmas                         false
% 3.94/0.98  --sat_fm_prep                           false
% 3.94/0.98  --sat_fm_uc_incr                        true
% 3.94/0.98  --sat_out_model                         small
% 3.94/0.98  --sat_out_clauses                       false
% 3.94/0.98  
% 3.94/0.98  ------ QBF Options
% 3.94/0.98  
% 3.94/0.98  --qbf_mode                              false
% 3.94/0.98  --qbf_elim_univ                         false
% 3.94/0.98  --qbf_dom_inst                          none
% 3.94/0.98  --qbf_dom_pre_inst                      false
% 3.94/0.98  --qbf_sk_in                             false
% 3.94/0.98  --qbf_pred_elim                         true
% 3.94/0.98  --qbf_split                             512
% 3.94/0.98  
% 3.94/0.98  ------ BMC1 Options
% 3.94/0.98  
% 3.94/0.98  --bmc1_incremental                      false
% 3.94/0.98  --bmc1_axioms                           reachable_all
% 3.94/0.98  --bmc1_min_bound                        0
% 3.94/0.98  --bmc1_max_bound                        -1
% 3.94/0.98  --bmc1_max_bound_default                -1
% 3.94/0.98  --bmc1_symbol_reachability              true
% 3.94/0.98  --bmc1_property_lemmas                  false
% 3.94/0.98  --bmc1_k_induction                      false
% 3.94/0.98  --bmc1_non_equiv_states                 false
% 3.94/0.98  --bmc1_deadlock                         false
% 3.94/0.98  --bmc1_ucm                              false
% 3.94/0.98  --bmc1_add_unsat_core                   none
% 3.94/0.98  --bmc1_unsat_core_children              false
% 3.94/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.98  --bmc1_out_stat                         full
% 3.94/0.98  --bmc1_ground_init                      false
% 3.94/0.98  --bmc1_pre_inst_next_state              false
% 3.94/0.98  --bmc1_pre_inst_state                   false
% 3.94/0.98  --bmc1_pre_inst_reach_state             false
% 3.94/0.98  --bmc1_out_unsat_core                   false
% 3.94/0.98  --bmc1_aig_witness_out                  false
% 3.94/0.98  --bmc1_verbose                          false
% 3.94/0.98  --bmc1_dump_clauses_tptp                false
% 3.94/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.98  --bmc1_dump_file                        -
% 3.94/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.98  --bmc1_ucm_extend_mode                  1
% 3.94/0.98  --bmc1_ucm_init_mode                    2
% 3.94/0.98  --bmc1_ucm_cone_mode                    none
% 3.94/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.98  --bmc1_ucm_relax_model                  4
% 3.94/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.98  --bmc1_ucm_layered_model                none
% 3.94/0.98  --bmc1_ucm_max_lemma_size               10
% 3.94/0.98  
% 3.94/0.98  ------ AIG Options
% 3.94/0.98  
% 3.94/0.98  --aig_mode                              false
% 3.94/0.98  
% 3.94/0.98  ------ Instantiation Options
% 3.94/0.98  
% 3.94/0.98  --instantiation_flag                    true
% 3.94/0.98  --inst_sos_flag                         false
% 3.94/0.98  --inst_sos_phase                        true
% 3.94/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.98  --inst_lit_sel_side                     none
% 3.94/0.98  --inst_solver_per_active                1400
% 3.94/0.98  --inst_solver_calls_frac                1.
% 3.94/0.98  --inst_passive_queue_type               priority_queues
% 3.94/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.98  --inst_passive_queues_freq              [25;2]
% 3.94/0.98  --inst_dismatching                      true
% 3.94/0.98  --inst_eager_unprocessed_to_passive     true
% 3.94/0.98  --inst_prop_sim_given                   true
% 3.94/0.98  --inst_prop_sim_new                     false
% 3.94/0.98  --inst_subs_new                         false
% 3.94/0.98  --inst_eq_res_simp                      false
% 3.94/0.98  --inst_subs_given                       false
% 3.94/0.98  --inst_orphan_elimination               true
% 3.94/0.98  --inst_learning_loop_flag               true
% 3.94/0.98  --inst_learning_start                   3000
% 3.94/0.98  --inst_learning_factor                  2
% 3.94/0.98  --inst_start_prop_sim_after_learn       3
% 3.94/0.98  --inst_sel_renew                        solver
% 3.94/0.98  --inst_lit_activity_flag                true
% 3.94/0.98  --inst_restr_to_given                   false
% 3.94/0.98  --inst_activity_threshold               500
% 3.94/0.98  --inst_out_proof                        true
% 3.94/0.98  
% 3.94/0.98  ------ Resolution Options
% 3.94/0.98  
% 3.94/0.98  --resolution_flag                       false
% 3.94/0.98  --res_lit_sel                           adaptive
% 3.94/0.98  --res_lit_sel_side                      none
% 3.94/0.98  --res_ordering                          kbo
% 3.94/0.98  --res_to_prop_solver                    active
% 3.94/0.98  --res_prop_simpl_new                    false
% 3.94/0.98  --res_prop_simpl_given                  true
% 3.94/0.98  --res_passive_queue_type                priority_queues
% 3.94/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.98  --res_passive_queues_freq               [15;5]
% 3.94/0.98  --res_forward_subs                      full
% 3.94/0.98  --res_backward_subs                     full
% 3.94/0.98  --res_forward_subs_resolution           true
% 3.94/0.98  --res_backward_subs_resolution          true
% 3.94/0.98  --res_orphan_elimination                true
% 3.94/0.98  --res_time_limit                        2.
% 3.94/0.98  --res_out_proof                         true
% 3.94/0.98  
% 3.94/0.98  ------ Superposition Options
% 3.94/0.98  
% 3.94/0.98  --superposition_flag                    true
% 3.94/0.98  --sup_passive_queue_type                priority_queues
% 3.94/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.98  --demod_completeness_check              fast
% 3.94/0.98  --demod_use_ground                      true
% 3.94/0.98  --sup_to_prop_solver                    passive
% 3.94/0.98  --sup_prop_simpl_new                    true
% 3.94/0.98  --sup_prop_simpl_given                  true
% 3.94/0.98  --sup_fun_splitting                     false
% 3.94/0.98  --sup_smt_interval                      50000
% 3.94/0.98  
% 3.94/0.98  ------ Superposition Simplification Setup
% 3.94/0.98  
% 3.94/0.98  --sup_indices_passive                   []
% 3.94/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_full_bw                           [BwDemod]
% 3.94/0.98  --sup_immed_triv                        [TrivRules]
% 3.94/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_immed_bw_main                     []
% 3.94/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.94/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.94/0.98  
% 3.94/0.98  ------ Combination Options
% 3.94/0.98  
% 3.94/0.98  --comb_res_mult                         3
% 3.94/0.98  --comb_sup_mult                         2
% 3.94/0.98  --comb_inst_mult                        10
% 3.94/0.98  
% 3.94/0.98  ------ Debug Options
% 3.94/0.98  
% 3.94/0.98  --dbg_backtrace                         false
% 3.94/0.98  --dbg_dump_prop_clauses                 false
% 3.94/0.98  --dbg_dump_prop_clauses_file            -
% 3.94/0.98  --dbg_out_stat                          false
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  ------ Proving...
% 3.94/0.98  
% 3.94/0.98  
% 3.94/0.98  % SZS status Theorem for theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.98  
% 3.94/0.98  fof(f7,axiom,(
% 3.94/0.98    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 3.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f28,plain,(
% 3.94/0.98    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 3.94/0.98    inference(ennf_transformation,[],[f7])).
% 3.94/0.98  
% 3.94/0.98  fof(f73,plain,(
% 3.94/0.98    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 3.94/0.98    inference(cnf_transformation,[],[f28])).
% 3.94/0.98  
% 3.94/0.98  fof(f13,conjecture,(
% 3.94/0.98    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.98  
% 3.94/0.98  fof(f14,negated_conjecture,(
% 3.94/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.94/0.98    inference(negated_conjecture,[],[f13])).
% 3.94/0.98  
% 3.94/0.98  fof(f16,plain,(
% 3.94/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.94/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.94/0.98  
% 3.94/0.98  fof(f17,plain,(
% 3.94/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.94/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.94/0.98  
% 3.94/0.98  fof(f18,plain,(
% 3.94/0.98    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 3.94/0.98    inference(pure_predicate_removal,[],[f17])).
% 3.94/0.98  
% 3.94/0.98  fof(f37,plain,(
% 3.94/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 3.94/0.98    inference(ennf_transformation,[],[f18])).
% 3.94/0.98  
% 3.94/0.98  fof(f38,plain,(
% 3.94/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.94/0.98    inference(flattening,[],[f37])).
% 3.94/0.98  
% 3.94/0.98  fof(f57,plain,(
% 3.94/0.98    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f38])).
% 3.94/0.99  
% 3.94/0.99  fof(f58,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 3.94/0.99    inference(flattening,[],[f57])).
% 3.94/0.99  
% 3.94/0.99  fof(f60,plain,(
% 3.94/0.99    ( ! [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(X0),sK7) | ~v1_subset_1(sK7,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),sK7) | v1_subset_1(sK7,u1_struct_0(X0))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(sK7,X0) & ~v1_xboole_0(sK7))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f59,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK6),X1) | ~v1_subset_1(X1,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),X1) | v1_subset_1(X1,u1_struct_0(sK6))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(X1,sK6) & ~v1_xboole_0(X1)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f61,plain,(
% 3.94/0.99    ((r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))) & (~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) & v13_waybel_0(sK7,sK6) & ~v1_xboole_0(sK7)) & l1_orders_2(sK6) & v1_yellow_0(sK6) & v5_orders_2(sK6) & ~v2_struct_0(sK6)),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f58,f60,f59])).
% 3.94/0.99  
% 3.94/0.99  fof(f95,plain,(
% 3.94/0.99    l1_orders_2(sK6)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f9,axiom,(
% 3.94/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f15,plain,(
% 3.94/0.99    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 3.94/0.99    inference(rectify,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f30,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f15])).
% 3.94/0.99  
% 3.94/0.99  fof(f31,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.94/0.99    inference(flattening,[],[f30])).
% 3.94/0.99  
% 3.94/0.99  fof(f49,plain,(
% 3.94/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f50,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f76,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f101,plain,(
% 3.94/0.99    ( ! [X4,X2,X0] : (r1_orders_2(X0,k1_yellow_0(X0,X2),X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.94/0.99    inference(equality_resolution,[],[f76])).
% 3.94/0.99  
% 3.94/0.99  fof(f8,axiom,(
% 3.94/0.99    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f29,plain,(
% 3.94/0.99    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f8])).
% 3.94/0.99  
% 3.94/0.99  fof(f74,plain,(
% 3.94/0.99    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f93,plain,(
% 3.94/0.99    v5_orders_2(sK6)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f92,plain,(
% 3.94/0.99    ~v2_struct_0(sK6)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f94,plain,(
% 3.94/0.99    v1_yellow_0(sK6)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f10,axiom,(
% 3.94/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f19,plain,(
% 3.94/0.99    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 3.94/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.94/0.99  
% 3.94/0.99  fof(f32,plain,(
% 3.94/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f19])).
% 3.94/0.99  
% 3.94/0.99  fof(f33,plain,(
% 3.94/0.99    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 3.94/0.99    inference(flattening,[],[f32])).
% 3.94/0.99  
% 3.94/0.99  fof(f83,plain,(
% 3.94/0.99    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f33])).
% 3.94/0.99  
% 3.94/0.99  fof(f3,axiom,(
% 3.94/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f20,plain,(
% 3.94/0.99    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f3])).
% 3.94/0.99  
% 3.94/0.99  fof(f21,plain,(
% 3.94/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(flattening,[],[f20])).
% 3.94/0.99  
% 3.94/0.99  fof(f43,plain,(
% 3.94/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f44,plain,(
% 3.94/0.99    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f43])).
% 3.94/0.99  
% 3.94/0.99  fof(f65,plain,(
% 3.94/0.99    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f44])).
% 3.94/0.99  
% 3.94/0.99  fof(f98,plain,(
% 3.94/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f11,axiom,(
% 3.94/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f34,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f11])).
% 3.94/0.99  
% 3.94/0.99  fof(f35,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(flattening,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f51,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f35])).
% 3.94/0.99  
% 3.94/0.99  fof(f52,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(rectify,[],[f51])).
% 3.94/0.99  
% 3.94/0.99  fof(f54,plain,(
% 3.94/0.99    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,X2,sK5(X0,X1)) & r2_hidden(X2,X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f53,plain,(
% 3.94/0.99    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK4(X0,X1),X3) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f55,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK5(X0,X1),X1) & r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).
% 3.94/0.99  
% 3.94/0.99  fof(f84,plain,(
% 3.94/0.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f55])).
% 3.94/0.99  
% 3.94/0.99  fof(f5,axiom,(
% 3.94/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f24,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.94/0.99    inference(ennf_transformation,[],[f5])).
% 3.94/0.99  
% 3.94/0.99  fof(f25,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.94/0.99    inference(flattening,[],[f24])).
% 3.94/0.99  
% 3.94/0.99  fof(f68,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f25])).
% 3.94/0.99  
% 3.94/0.99  fof(f97,plain,(
% 3.94/0.99    v13_waybel_0(sK7,sK6)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f6,axiom,(
% 3.94/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f26,plain,(
% 3.94/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f6])).
% 3.94/0.99  
% 3.94/0.99  fof(f27,plain,(
% 3.94/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(flattening,[],[f26])).
% 3.94/0.99  
% 3.94/0.99  fof(f45,plain,(
% 3.94/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f27])).
% 3.94/0.99  
% 3.94/0.99  fof(f46,plain,(
% 3.94/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(rectify,[],[f45])).
% 3.94/0.99  
% 3.94/0.99  fof(f47,plain,(
% 3.94/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f48,plain,(
% 3.94/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 3.94/0.99  
% 3.94/0.99  fof(f71,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f48])).
% 3.94/0.99  
% 3.94/0.99  fof(f75,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X2,X1) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f50])).
% 3.94/0.99  
% 3.94/0.99  fof(f102,plain,(
% 3.94/0.99    ( ! [X2,X0] : (r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 3.94/0.99    inference(equality_resolution,[],[f75])).
% 3.94/0.99  
% 3.94/0.99  fof(f69,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f48])).
% 3.94/0.99  
% 3.94/0.99  fof(f1,axiom,(
% 3.94/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f39,plain,(
% 3.94/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.94/0.99    inference(nnf_transformation,[],[f1])).
% 3.94/0.99  
% 3.94/0.99  fof(f40,plain,(
% 3.94/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.94/0.99    inference(rectify,[],[f39])).
% 3.94/0.99  
% 3.94/0.99  fof(f41,plain,(
% 3.94/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f42,plain,(
% 3.94/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f62,plain,(
% 3.94/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f42])).
% 3.94/0.99  
% 3.94/0.99  fof(f2,axiom,(
% 3.94/0.99    v1_xboole_0(k1_xboole_0)),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f64,plain,(
% 3.94/0.99    v1_xboole_0(k1_xboole_0)),
% 3.94/0.99    inference(cnf_transformation,[],[f2])).
% 3.94/0.99  
% 3.94/0.99  fof(f96,plain,(
% 3.94/0.99    ~v1_xboole_0(sK7)),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f12,axiom,(
% 3.94/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f36,plain,(
% 3.94/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f12])).
% 3.94/0.99  
% 3.94/0.99  fof(f56,plain,(
% 3.94/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(nnf_transformation,[],[f36])).
% 3.94/0.99  
% 3.94/0.99  fof(f91,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f56])).
% 3.94/0.99  
% 3.94/0.99  fof(f100,plain,(
% 3.94/0.99    r2_hidden(k3_yellow_0(sK6),sK7) | ~v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  fof(f4,axiom,(
% 3.94/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f22,plain,(
% 3.94/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.94/0.99    inference(ennf_transformation,[],[f4])).
% 3.94/0.99  
% 3.94/0.99  fof(f23,plain,(
% 3.94/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.94/0.99    inference(flattening,[],[f22])).
% 3.94/0.99  
% 3.94/0.99  fof(f67,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f23])).
% 3.94/0.99  
% 3.94/0.99  fof(f66,plain,(
% 3.94/0.99    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f44])).
% 3.94/0.99  
% 3.94/0.99  fof(f90,plain,(
% 3.94/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f56])).
% 3.94/0.99  
% 3.94/0.99  fof(f103,plain,(
% 3.94/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.94/0.99    inference(equality_resolution,[],[f90])).
% 3.94/0.99  
% 3.94/0.99  fof(f99,plain,(
% 3.94/0.99    ~r2_hidden(k3_yellow_0(sK6),sK7) | v1_subset_1(sK7,u1_struct_0(sK6))),
% 3.94/0.99    inference(cnf_transformation,[],[f61])).
% 3.94/0.99  
% 3.94/0.99  cnf(c_11,plain,
% 3.94/0.99      ( ~ l1_orders_2(X0)
% 3.94/0.99      | k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_35,negated_conjecture,
% 3.94/0.99      ( l1_orders_2(sK6) ),
% 3.94/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1089,plain,
% 3.94/0.99      ( k1_yellow_0(X0,k1_xboole_0) = k3_yellow_0(X0) | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1090,plain,
% 3.94/0.99      ( k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1089]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_19,plain,
% 3.94/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.94/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_12,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_238,plain,
% 3.94/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.94/0.99      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_19,c_12]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_239,plain,
% 3.94/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.94/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_238]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_37,negated_conjecture,
% 3.94/0.99      ( v5_orders_2(sK6) ),
% 3.94/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_638,plain,
% 3.94/0.99      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 3.94/0.99      | ~ r2_lattice3(X0,X1,X2)
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ l1_orders_2(X0)
% 3.94/0.99      | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_239,c_37]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_639,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
% 3.94/0.99      | ~ r2_lattice3(sK6,X0,X1)
% 3.94/0.99      | ~ r1_yellow_0(sK6,X0)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ l1_orders_2(sK6) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_638]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_643,plain,
% 3.94/0.99      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ r1_yellow_0(sK6,X0)
% 3.94/0.99      | ~ r2_lattice3(sK6,X0,X1)
% 3.94/0.99      | r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_639,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_644,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1)
% 3.94/0.99      | ~ r2_lattice3(sK6,X0,X1)
% 3.94/0.99      | ~ r1_yellow_0(sK6,X0)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_643]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3332,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,X0),X1) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,X0,X1) != iProver_top
% 3.94/0.99      | r1_yellow_0(sK6,X0) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3958,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.94/0.99      | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1090,c_3332]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_38,negated_conjecture,
% 3.94/0.99      ( ~ v2_struct_0(sK6) ),
% 3.94/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_39,plain,
% 3.94/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_40,plain,
% 3.94/0.99      ( v5_orders_2(sK6) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_36,negated_conjecture,
% 3.94/0.99      ( v1_yellow_0(sK6) ),
% 3.94/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_41,plain,
% 3.94/0.99      ( v1_yellow_0(sK6) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_42,plain,
% 3.94/0.99      ( l1_orders_2(sK6) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_21,plain,
% 3.94/0.99      ( r1_yellow_0(X0,k1_xboole_0)
% 3.94/0.99      | v2_struct_0(X0)
% 3.94/0.99      | ~ v1_yellow_0(X0)
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_70,plain,
% 3.94/0.99      ( r1_yellow_0(X0,k1_xboole_0) = iProver_top
% 3.94/0.99      | v2_struct_0(X0) = iProver_top
% 3.94/0.99      | v1_yellow_0(X0) != iProver_top
% 3.94/0.99      | v5_orders_2(X0) != iProver_top
% 3.94/0.99      | l1_orders_2(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_72,plain,
% 3.94/0.99      ( r1_yellow_0(sK6,k1_xboole_0) = iProver_top
% 3.94/0.99      | v2_struct_0(sK6) = iProver_top
% 3.94/0.99      | v1_yellow_0(sK6) != iProver_top
% 3.94/0.99      | v5_orders_2(sK6) != iProver_top
% 3.94/0.99      | l1_orders_2(sK6) != iProver_top ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4085,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.94/0.99      | r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3958,c_39,c_40,c_41,c_42,c_72]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4086,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k3_yellow_0(sK6),X0) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,k1_xboole_0,X0) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_4085]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | m1_subset_1(sK1(X1,X0),X1)
% 3.94/0.99      | X0 = X1 ),
% 3.94/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3341,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK1(X1,X0),X1) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_32,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3338,plain,
% 3.94/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_27,plain,
% 3.94/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.94/0.99      | ~ v13_waybel_0(X3,X0)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.94/0.99      | ~ r2_hidden(X1,X3)
% 3.94/0.99      | r2_hidden(X2,X3)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1040,plain,
% 3.94/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.94/0.99      | ~ v13_waybel_0(X3,X0)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 3.94/0.99      | ~ r2_hidden(X1,X3)
% 3.94/0.99      | r2_hidden(X2,X3)
% 3.94/0.99      | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1041,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ v13_waybel_0(X2,sK6)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(X0,X2)
% 3.94/0.99      | r2_hidden(X1,X2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1040]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6,plain,
% 3.94/0.99      ( m1_subset_1(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.94/0.99      | ~ r2_hidden(X0,X2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1057,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ v13_waybel_0(X2,sK6)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(X0,X2)
% 3.94/0.99      | r2_hidden(X1,X2) ),
% 3.94/0.99      inference(forward_subsumption_resolution,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_1041,c_6]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3324,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.94/0.99      | v13_waybel_0(X2,sK6) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.94/0.99      | r2_hidden(X1,X2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5273,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.94/0.99      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.94/0.99      | r2_hidden(X1,sK7) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3338,c_3324]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_45,plain,
% 3.94/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_33,negated_conjecture,
% 3.94/0.99      ( v13_waybel_0(sK7,sK6) ),
% 3.94/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1268,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(X0,X2)
% 3.94/0.99      | r2_hidden(X1,X2)
% 3.94/0.99      | sK7 != X2
% 3.94/0.99      | sK6 != sK6 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_1057]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1269,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(X0,sK7)
% 3.94/0.99      | r2_hidden(X1,sK7) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1268]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1270,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.94/0.99      | r2_hidden(X1,sK7) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5394,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.94/0.99      | r2_hidden(X1,sK7) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_5273,c_45,c_1270]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5402,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = X0
% 3.94/0.99      | r1_orders_2(sK6,X1,sK1(u1_struct_0(sK6),X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(X1,sK7) != iProver_top
% 3.94/0.99      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3341,c_5394]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8726,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = X0
% 3.94/0.99      | r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4086,c_5402]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2742,plain,
% 3.94/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.94/0.99      theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2757,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = u1_struct_0(sK6) | sK6 != sK6 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2742]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2733,plain,( X0 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2766,plain,
% 3.94/0.99      ( sK6 = sK6 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2733]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3848,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6))
% 3.94/0.99      | X0 = u1_struct_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3854,plain,
% 3.94/0.99      ( X0 = u1_struct_0(sK6)
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3848]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2734,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4327,plain,
% 3.94/0.99      ( X0 != X1 | u1_struct_0(sK6) != X1 | u1_struct_0(sK6) = X0 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2734]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5992,plain,
% 3.94/0.99      ( X0 != u1_struct_0(sK6)
% 3.94/0.99      | u1_struct_0(sK6) = X0
% 3.94/0.99      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4327]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_8,plain,
% 3.94/0.99      ( r2_lattice3(X0,X1,X2)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1130,plain,
% 3.94/0.99      ( r2_lattice3(X0,X1,X2)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.94/0.99      | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1131,plain,
% 3.94/0.99      ( r2_lattice3(sK6,X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | r2_hidden(sK2(sK6,X0,X1),X0) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1130]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3319,plain,
% 3.94/0.99      ( r2_lattice3(sK6,X0,X1) = iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(sK2(sK6,X0,X1),X0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_20,plain,
% 3.94/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_231,plain,
% 3.94/0.99      ( ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_20,c_12]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_232,plain,
% 3.94/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ v5_orders_2(X0)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_231]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_662,plain,
% 3.94/0.99      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 3.94/0.99      | ~ r1_yellow_0(X0,X1)
% 3.94/0.99      | ~ l1_orders_2(X0)
% 3.94/0.99      | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_232,c_37]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_663,plain,
% 3.94/0.99      ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0))
% 3.94/0.99      | ~ r1_yellow_0(sK6,X0)
% 3.94/0.99      | ~ l1_orders_2(sK6) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_662]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_667,plain,
% 3.94/0.99      ( ~ r1_yellow_0(sK6,X0) | r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_663,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_668,plain,
% 3.94/0.99      ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) | ~ r1_yellow_0(sK6,X0) ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_667]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3331,plain,
% 3.94/0.99      ( r2_lattice3(sK6,X0,k1_yellow_0(sK6,X0)) = iProver_top
% 3.94/0.99      | r1_yellow_0(sK6,X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3725,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top
% 3.94/0.99      | r1_yellow_0(sK6,k1_xboole_0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1090,c_3331]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3893,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,k3_yellow_0(sK6)) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3725,c_39,c_40,c_41,c_42,c_72]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1080,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1081,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1080]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3322,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3684,plain,
% 3.94/0.99      ( m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1090,c_3322]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_10,plain,
% 3.94/0.99      ( r1_orders_2(X0,X1,X2)
% 3.94/0.99      | ~ r2_lattice3(X0,X3,X2)
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.94/0.99      | ~ r2_hidden(X1,X3)
% 3.94/0.99      | ~ l1_orders_2(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1094,plain,
% 3.94/0.99      ( r1_orders_2(X0,X1,X2)
% 3.94/0.99      | ~ r2_lattice3(X0,X3,X2)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.94/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.94/0.99      | ~ r2_hidden(X1,X3)
% 3.94/0.99      | sK6 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1095,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ r2_lattice3(sK6,X2,X1)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.94/0.99      | ~ r2_hidden(X0,X2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_1094]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3321,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,X1) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,X2,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1095]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4304,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,X1,k3_yellow_0(sK6)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3684,c_3321]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6601,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,k3_yellow_0(sK6)) = iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3893,c_4304]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2,plain,
% 3.94/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_566,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_567,plain,
% 3.94/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_566]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_568,plain,
% 3.94/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6616,plain,
% 3.94/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_6601,c_568]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6622,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,X0) = iProver_top
% 3.94/0.99      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3319,c_6616]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6880,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = X0
% 3.94/0.99      | r2_lattice3(sK6,k1_xboole_0,sK1(u1_struct_0(sK6),X0)) = iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3341,c_6622]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5405,plain,
% 3.94/0.99      ( r1_orders_2(sK6,X0,k1_yellow_0(sK6,X1)) != iProver_top
% 3.94/0.99      | r2_hidden(X0,sK7) != iProver_top
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,X1),sK7) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3322,c_5394]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6389,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_4086,c_5405]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_34,negated_conjecture,
% 3.94/0.99      ( ~ v1_xboole_0(sK7) ),
% 3.94/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_43,plain,
% 3.94/0.99      ( v1_xboole_0(sK7) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_44,plain,
% 3.94/0.99      ( v13_waybel_0(sK7,sK6) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_101,plain,
% 3.94/0.99      ( ~ l1_orders_2(sK6)
% 3.94/0.99      | k1_yellow_0(sK6,k1_xboole_0) = k3_yellow_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_28,plain,
% 3.94/0.99      ( v1_subset_1(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | X0 = X1 ),
% 3.94/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_30,negated_conjecture,
% 3.94/0.99      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.94/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_311,plain,
% 3.94/0.99      ( ~ v1_subset_1(sK7,u1_struct_0(sK6))
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.94/0.99      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_604,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.94/0.99      | X1 = X0
% 3.94/0.99      | u1_struct_0(sK6) != X1
% 3.94/0.99      | sK7 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_311]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_605,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7)
% 3.94/0.99      | u1_struct_0(sK6) = sK7 ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_604]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_606,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = sK7
% 3.94/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1082,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3782,plain,
% 3.94/0.99      ( sK7 = sK7 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2733]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3620,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.94/0.99      | ~ r2_lattice3(sK6,k1_xboole_0,X0)
% 3.94/0.99      | ~ r1_yellow_0(sK6,k1_xboole_0)
% 3.94/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_644]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3831,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0))
% 3.94/0.99      | ~ r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0))
% 3.94/0.99      | ~ r1_yellow_0(sK6,k1_xboole_0)
% 3.94/0.99      | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3620]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3836,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0)) = iProver_top
% 3.94/0.99      | r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) != iProver_top
% 3.94/0.99      | r1_yellow_0(sK6,k1_xboole_0) != iProver_top
% 3.94/0.99      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3831]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3732,plain,
% 3.94/0.99      ( u1_struct_0(sK6) != X0 | sK7 != X0 | sK7 = u1_struct_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2734]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5215,plain,
% 3.94/0.99      ( u1_struct_0(sK6) != sK7 | sK7 = u1_struct_0(sK6) | sK7 != sK7 ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3732]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2738,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.94/0.99      theory(equality) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4488,plain,
% 3.94/0.99      ( m1_subset_1(X0,X1)
% 3.94/0.99      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.94/0.99      | X0 != k3_yellow_0(sK6)
% 3.94/0.99      | X1 != u1_struct_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_2738]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5039,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.94/0.99      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.94/0.99      | X0 != u1_struct_0(sK6)
% 3.94/0.99      | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_4488]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6076,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7)
% 3.94/0.99      | ~ m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6))
% 3.94/0.99      | k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
% 3.94/0.99      | sK7 != u1_struct_0(sK6) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_5039]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6078,plain,
% 3.94/0.99      ( k1_yellow_0(sK6,k1_xboole_0) != k3_yellow_0(sK6)
% 3.94/0.99      | sK7 != u1_struct_0(sK6)
% 3.94/0.99      | m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7) = iProver_top
% 3.94/0.99      | m1_subset_1(k3_yellow_0(sK6),u1_struct_0(sK6)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6076]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3691,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) | v1_xboole_0(sK7) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6077,plain,
% 3.94/0.99      ( ~ m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7)
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7)
% 3.94/0.99      | v1_xboole_0(sK7) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3691]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6080,plain,
% 3.94/0.99      ( m1_subset_1(k1_yellow_0(sK6,k1_xboole_0),sK7) != iProver_top
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6077]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3673,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,X0,X1)
% 3.94/0.99      | ~ v13_waybel_0(sK7,sK6)
% 3.94/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(X0,sK7)
% 3.94/0.99      | r2_hidden(X1,sK7) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_1057]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6061,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),X0)
% 3.94/0.99      | ~ v13_waybel_0(sK7,sK6)
% 3.94/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | r2_hidden(X0,sK7)
% 3.94/0.99      | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_3673]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6631,plain,
% 3.94/0.99      ( ~ r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0))
% 3.94/0.99      | ~ v13_waybel_0(sK7,sK6)
% 3.94/0.99      | ~ m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6))
% 3.94/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,X0),sK7)
% 3.94/0.99      | ~ r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_6061]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6632,plain,
% 3.94/0.99      ( r1_orders_2(sK6,k1_yellow_0(sK6,k1_xboole_0),k1_yellow_0(sK6,X0)) != iProver_top
% 3.94/0.99      | v13_waybel_0(sK7,sK6) != iProver_top
% 3.94/0.99      | m1_subset_1(k1_yellow_0(sK6,X0),u1_struct_0(sK6)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top
% 3.94/0.99      | r2_hidden(k1_yellow_0(sK6,k1_xboole_0),sK7) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_6631]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6884,plain,
% 3.94/0.99      ( r2_lattice3(sK6,k1_xboole_0,k1_yellow_0(sK6,X0)) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3322,c_6622]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_7442,plain,
% 3.94/0.99      ( r2_hidden(k1_yellow_0(sK6,X0),sK7) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_6389,c_39,c_40,c_41,c_35,c_42,c_43,c_44,c_45,c_72,
% 3.94/0.99                 c_101,c_606,c_1082,c_3684,c_3782,c_3836,c_5215,c_6078,
% 3.94/0.99                 c_6080,c_6632,c_6884]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_7449,plain,
% 3.94/0.99      ( r2_hidden(k3_yellow_0(sK6),sK7) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1090,c_7442]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13065,plain,
% 3.94/0.99      ( r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top
% 3.94/0.99      | u1_struct_0(sK6) = X0
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_8726,c_2757,c_2766,c_3854,c_5992,c_6880,c_7449]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13066,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = X0
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(sK1(u1_struct_0(sK6),X0),sK7) = iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_13065]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | ~ r2_hidden(sK1(X1,X0),X0)
% 3.94/0.99      | X0 = X1 ),
% 3.94/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3342,plain,
% 3.94/0.99      ( X0 = X1
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.94/0.99      | r2_hidden(sK1(X1,X0),X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13075,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = sK7
% 3.94/0.99      | m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_13066,c_3342]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13288,plain,
% 3.94/0.99      ( u1_struct_0(sK6) = sK7 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_13075,c_45]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_29,plain,
% 3.94/0.99      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_31,negated_conjecture,
% 3.94/0.99      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.94/0.99      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.94/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_309,plain,
% 3.94/0.99      ( v1_subset_1(sK7,u1_struct_0(sK6))
% 3.94/0.99      | ~ r2_hidden(k3_yellow_0(sK6),sK7) ),
% 3.94/0.99      inference(prop_impl,[status(thm)],[c_31]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_618,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 3.94/0.99      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.94/0.99      | u1_struct_0(sK6) != X0
% 3.94/0.99      | sK7 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_309]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_619,plain,
% 3.94/0.99      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.94/0.99      | ~ r2_hidden(k3_yellow_0(sK6),sK7)
% 3.94/0.99      | sK7 != u1_struct_0(sK6) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3333,plain,
% 3.94/0.99      ( sK7 != u1_struct_0(sK6)
% 3.94/0.99      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13347,plain,
% 3.94/0.99      ( sK7 != sK7
% 3.94/0.99      | m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_13288,c_3333]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13535,plain,
% 3.94/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) != iProver_top
% 3.94/0.99      | r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_13347]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13374,plain,
% 3.94/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(sK7)) = iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_13288,c_3338]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_13538,plain,
% 3.94/0.99      ( r2_hidden(k3_yellow_0(sK6),sK7) != iProver_top ),
% 3.94/0.99      inference(forward_subsumption_resolution,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_13535,c_13374]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(contradiction,plain,
% 3.94/0.99      ( $false ),
% 3.94/0.99      inference(minisat,[status(thm)],[c_13538,c_7449]) ).
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  ------                               Statistics
% 3.94/0.99  
% 3.94/0.99  ------ General
% 3.94/0.99  
% 3.94/0.99  abstr_ref_over_cycles:                  0
% 3.94/0.99  abstr_ref_under_cycles:                 0
% 3.94/0.99  gc_basic_clause_elim:                   0
% 3.94/0.99  forced_gc_time:                         0
% 3.94/0.99  parsing_time:                           0.015
% 3.94/0.99  unif_index_cands_time:                  0.
% 3.94/0.99  unif_index_add_time:                    0.
% 3.94/0.99  orderings_time:                         0.
% 3.94/0.99  out_proof_time:                         0.014
% 3.94/0.99  total_time:                             0.442
% 3.94/0.99  num_of_symbols:                         56
% 3.94/0.99  num_of_terms:                           10707
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing
% 3.94/0.99  
% 3.94/0.99  num_of_splits:                          0
% 3.94/0.99  num_of_split_atoms:                     0
% 3.94/0.99  num_of_reused_defs:                     0
% 3.94/0.99  num_eq_ax_congr_red:                    38
% 3.94/0.99  num_of_sem_filtered_clauses:            1
% 3.94/0.99  num_of_subtypes:                        0
% 3.94/0.99  monotx_restored_types:                  0
% 3.94/0.99  sat_num_of_epr_types:                   0
% 3.94/0.99  sat_num_of_non_cyclic_types:            0
% 3.94/0.99  sat_guarded_non_collapsed_types:        0
% 3.94/0.99  num_pure_diseq_elim:                    0
% 3.94/0.99  simp_replaced_by:                       0
% 3.94/0.99  res_preprocessed:                       173
% 3.94/0.99  prep_upred:                             0
% 3.94/0.99  prep_unflattend:                        90
% 3.94/0.99  smt_new_axioms:                         0
% 3.94/0.99  pred_elim_cands:                        7
% 3.94/0.99  pred_elim:                              5
% 3.94/0.99  pred_elim_cl:                           6
% 3.94/0.99  pred_elim_cycles:                       13
% 3.94/0.99  merged_defs:                            2
% 3.94/0.99  merged_defs_ncl:                        0
% 3.94/0.99  bin_hyper_res:                          2
% 3.94/0.99  prep_cycles:                            4
% 3.94/0.99  pred_elim_time:                         0.056
% 3.94/0.99  splitting_time:                         0.
% 3.94/0.99  sem_filter_time:                        0.
% 3.94/0.99  monotx_time:                            0.001
% 3.94/0.99  subtype_inf_time:                       0.
% 3.94/0.99  
% 3.94/0.99  ------ Problem properties
% 3.94/0.99  
% 3.94/0.99  clauses:                                33
% 3.94/0.99  conjectures:                            3
% 3.94/0.99  epr:                                    6
% 3.94/0.99  horn:                                   19
% 3.94/0.99  ground:                                 8
% 3.94/0.99  unary:                                  7
% 3.94/0.99  binary:                                 4
% 3.94/0.99  lits:                                   93
% 3.94/0.99  lits_eq:                                8
% 3.94/0.99  fd_pure:                                0
% 3.94/0.99  fd_pseudo:                              0
% 3.94/0.99  fd_cond:                                0
% 3.94/0.99  fd_pseudo_cond:                         5
% 3.94/0.99  ac_symbols:                             0
% 3.94/0.99  
% 3.94/0.99  ------ Propositional Solver
% 3.94/0.99  
% 3.94/0.99  prop_solver_calls:                      29
% 3.94/0.99  prop_fast_solver_calls:                 2153
% 3.94/0.99  smt_solver_calls:                       0
% 3.94/0.99  smt_fast_solver_calls:                  0
% 3.94/0.99  prop_num_of_clauses:                    4414
% 3.94/0.99  prop_preprocess_simplified:             10165
% 3.94/0.99  prop_fo_subsumed:                       78
% 3.94/0.99  prop_solver_time:                       0.
% 3.94/0.99  smt_solver_time:                        0.
% 3.94/0.99  smt_fast_solver_time:                   0.
% 3.94/0.99  prop_fast_solver_time:                  0.
% 3.94/0.99  prop_unsat_core_time:                   0.
% 3.94/0.99  
% 3.94/0.99  ------ QBF
% 3.94/0.99  
% 3.94/0.99  qbf_q_res:                              0
% 3.94/0.99  qbf_num_tautologies:                    0
% 3.94/0.99  qbf_prep_cycles:                        0
% 3.94/0.99  
% 3.94/0.99  ------ BMC1
% 3.94/0.99  
% 3.94/0.99  bmc1_current_bound:                     -1
% 3.94/0.99  bmc1_last_solved_bound:                 -1
% 3.94/0.99  bmc1_unsat_core_size:                   -1
% 3.94/0.99  bmc1_unsat_core_parents_size:           -1
% 3.94/0.99  bmc1_merge_next_fun:                    0
% 3.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation
% 3.94/0.99  
% 3.94/0.99  inst_num_of_clauses:                    980
% 3.94/0.99  inst_num_in_passive:                    240
% 3.94/0.99  inst_num_in_active:                     596
% 3.94/0.99  inst_num_in_unprocessed:                144
% 3.94/0.99  inst_num_of_loops:                      660
% 3.94/0.99  inst_num_of_learning_restarts:          0
% 3.94/0.99  inst_num_moves_active_passive:          60
% 3.94/0.99  inst_lit_activity:                      0
% 3.94/0.99  inst_lit_activity_moves:                0
% 3.94/0.99  inst_num_tautologies:                   0
% 3.94/0.99  inst_num_prop_implied:                  0
% 3.94/0.99  inst_num_existing_simplified:           0
% 3.94/0.99  inst_num_eq_res_simplified:             0
% 3.94/0.99  inst_num_child_elim:                    0
% 3.94/0.99  inst_num_of_dismatching_blockings:      260
% 3.94/0.99  inst_num_of_non_proper_insts:           992
% 3.94/0.99  inst_num_of_duplicates:                 0
% 3.94/0.99  inst_inst_num_from_inst_to_res:         0
% 3.94/0.99  inst_dismatching_checking_time:         0.
% 3.94/0.99  
% 3.94/0.99  ------ Resolution
% 3.94/0.99  
% 3.94/0.99  res_num_of_clauses:                     0
% 3.94/0.99  res_num_in_passive:                     0
% 3.94/0.99  res_num_in_active:                      0
% 3.94/0.99  res_num_of_loops:                       177
% 3.94/0.99  res_forward_subset_subsumed:            98
% 3.94/0.99  res_backward_subset_subsumed:           0
% 3.94/0.99  res_forward_subsumed:                   0
% 3.94/0.99  res_backward_subsumed:                  0
% 3.94/0.99  res_forward_subsumption_resolution:     7
% 3.94/0.99  res_backward_subsumption_resolution:    0
% 3.94/0.99  res_clause_to_clause_subsumption:       1429
% 3.94/0.99  res_orphan_elimination:                 0
% 3.94/0.99  res_tautology_del:                      68
% 3.94/0.99  res_num_eq_res_simplified:              0
% 3.94/0.99  res_num_sel_changes:                    0
% 3.94/0.99  res_moves_from_active_to_pass:          0
% 3.94/0.99  
% 3.94/0.99  ------ Superposition
% 3.94/0.99  
% 3.94/0.99  sup_time_total:                         0.
% 3.94/0.99  sup_time_generating:                    0.
% 3.94/0.99  sup_time_sim_full:                      0.
% 3.94/0.99  sup_time_sim_immed:                     0.
% 3.94/0.99  
% 3.94/0.99  sup_num_of_clauses:                     228
% 3.94/0.99  sup_num_in_active:                      42
% 3.94/0.99  sup_num_in_passive:                     186
% 3.94/0.99  sup_num_of_loops:                       130
% 3.94/0.99  sup_fw_superposition:                   209
% 3.94/0.99  sup_bw_superposition:                   157
% 3.94/0.99  sup_immediate_simplified:               115
% 3.94/0.99  sup_given_eliminated:                   0
% 3.94/0.99  comparisons_done:                       0
% 3.94/0.99  comparisons_avoided:                    0
% 3.94/0.99  
% 3.94/0.99  ------ Simplifications
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  sim_fw_subset_subsumed:                 49
% 3.94/0.99  sim_bw_subset_subsumed:                 11
% 3.94/0.99  sim_fw_subsumed:                        45
% 3.94/0.99  sim_bw_subsumed:                        10
% 3.94/0.99  sim_fw_subsumption_res:                 2
% 3.94/0.99  sim_bw_subsumption_res:                 1
% 3.94/0.99  sim_tautology_del:                      31
% 3.94/0.99  sim_eq_tautology_del:                   3
% 3.94/0.99  sim_eq_res_simp:                        1
% 3.94/0.99  sim_fw_demodulated:                     0
% 3.94/0.99  sim_bw_demodulated:                     84
% 3.94/0.99  sim_light_normalised:                   11
% 3.94/0.99  sim_joinable_taut:                      0
% 3.94/0.99  sim_joinable_simp:                      0
% 3.94/0.99  sim_ac_normalised:                      0
% 3.94/0.99  sim_smt_subsumption:                    0
% 3.94/0.99  
%------------------------------------------------------------------------------
