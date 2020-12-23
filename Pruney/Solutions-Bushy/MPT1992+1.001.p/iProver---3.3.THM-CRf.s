%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1992+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:00 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  296 (4509 expanded)
%              Number of clauses        :  169 (1074 expanded)
%              Number of leaves         :   31 (1074 expanded)
%              Depth                    :   33
%              Number of atoms          : 1336 (44900 expanded)
%              Number of equality atoms :  162 ( 455 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v1_waybel_3(k4_yellow_0(X0),X0)
       => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          & ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_finset_1(X1)
                & ~ v1_xboole_0(X1) )
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                          & r2_hidden(X2,X1) ) )
                  & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X1)
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f29,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f75,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f76,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f75])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
            | ~ r2_hidden(X2,sK4)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r1_waybel_3(X0,k2_yellow_0(X0,sK4),k4_yellow_0(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,
    ( ? [X0] :
        ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & v1_waybel_3(k4_yellow_0(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(sK3,X2,k4_yellow_0(sK3))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
            & r1_waybel_3(sK3,k2_yellow_0(sK3,X1),k4_yellow_0(sK3))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(sK3),sK3)
      & l1_orders_2(sK3)
      & v3_waybel_3(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,
    ( ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
      | ( ! [X2] :
            ( ~ r3_orders_2(sK3,X2,k4_yellow_0(sK3))
            | ~ r2_hidden(X2,sK4)
            | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
        & r1_waybel_3(sK3,k2_yellow_0(sK3,sK4),k4_yellow_0(sK3))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
        & ~ v1_xboole_0(sK4) ) )
    & v1_waybel_3(k4_yellow_0(sK3),sK3)
    & l1_orders_2(sK3)
    & v3_waybel_3(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f76,f89,f88])).

fof(f129,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f128,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f130,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f131,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f132,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f133,plain,(
    v3_waybel_3(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f134,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f97,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v24_waybel_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ( v2_yellow_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f93,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( r2_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r2_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f136,plain,
    ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f69,f86])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f78])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f137,plain,
    ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f90])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f59])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r1_waybel_3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r1_waybel_3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f80])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_waybel_3(X1,sK1(X0,X1,X2),X2)
        & sK1(X0,X1,X2) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
          | ! [X3] :
              ( ~ r1_waybel_3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r1_waybel_3(X1,sK1(X0,X1,X2),X2)
            & sK1(X0,X1,X2) = X0
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f81,f82])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      | ~ r1_waybel_3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f140,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_waybel_3(X1,X2))
      | ~ r1_waybel_3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f115])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_3(X1,X0)
              | ~ r1_waybel_3(X0,X1,X1) )
            & ( r1_waybel_3(X0,X1,X1)
              | ~ v1_waybel_3(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_waybel_3(X0,X1,X1)
      | ~ v1_waybel_3(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f135,plain,(
    v1_waybel_3(k4_yellow_0(sK3),sK3) ),
    inference(cnf_transformation,[],[f90])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f85,plain,(
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
    inference(nnf_transformation,[],[f64])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f139,plain,(
    ! [X2] :
      ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
      | ~ r3_orders_2(sK3,X2,k4_yellow_0(sK3))
      | ~ r2_hidden(X2,sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_16,plain,
    ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_29,plain,
    ( r2_hidden(k4_yellow_0(X0),X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ v13_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_571,plain,
    ( r2_hidden(k4_yellow_0(X0),X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | X0 != X3
    | k4_waybel_0(X3,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_572,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_598,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_572,c_12])).

cnf(c_47,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_637,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_598,c_47])).

cnf(c_638,plain,
    ( r2_hidden(k4_yellow_0(sK3),k4_waybel_0(sK3,X0))
    | ~ v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v5_orders_2(sK3)
    | v1_xboole_0(k4_waybel_0(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v2_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_48,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_46,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_45,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_44,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_43,negated_conjecture,
    ( v3_waybel_3(sK3) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_42,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_4,plain,
    ( ~ v3_waybel_3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_154,plain,
    ( ~ v3_waybel_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v24_waybel_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_157,plain,
    ( ~ v2_lattice3(sK3)
    | ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v24_waybel_0(X0)
    | v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_162,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v24_waybel_0(sK3)
    | v2_yellow_0(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | r2_hidden(k4_yellow_0(sK3),k4_waybel_0(sK3,X0))
    | v1_xboole_0(k4_waybel_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_48,c_46,c_45,c_44,c_43,c_42,c_154,c_157,c_162])).

cnf(c_643,plain,
    ( r2_hidden(k4_yellow_0(sK3),k4_waybel_0(sK3,X0))
    | ~ v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_642])).

cnf(c_2112,plain,
    ( r2_hidden(k4_yellow_0(sK3),k4_waybel_0(sK3,X0)) = iProver_top
    | v2_waybel_0(k4_waybel_0(sK3,X0),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_26,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r2_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_40,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_781,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))) != X0
    | k1_waybel_3(sK3,k4_yellow_0(sK3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_40])).

cnf(c_782,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_2107,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_31,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2118,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3875,plain,
    ( r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2107,c_2118])).

cnf(c_1189,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4)
    | k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))) != X2
    | k1_waybel_3(sK3,k4_yellow_0(sK3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_782])).

cnf(c_1190,plain,
    ( ~ r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | ~ r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1189])).

cnf(c_36,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1204,plain,
    ( ~ r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | ~ r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v1_xboole_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1190,c_36,c_36])).

cnf(c_1208,plain,
    ( r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_15,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2120,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2119,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3626,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2120,c_2119])).

cnf(c_39,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_797,plain,
    ( r1_xboole_0(X0,X1)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))) != X0
    | k1_waybel_3(sK3,k4_yellow_0(sK3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_39])).

cnf(c_798,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_2106,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_3874,plain,
    ( r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_2118])).

cnf(c_55,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_13,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_130,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_132,plain,
    ( m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_555,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_44])).

cnf(c_556,plain,
    ( ~ v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_558,plain,
    ( ~ v2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_44,c_42,c_157])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_558])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_1055,plain,
    ( m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1051,c_42])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k5_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1055])).

cnf(c_2385,plain,
    ( m1_subset_1(k5_waybel_0(sK3,k4_yellow_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_2386,plain,
    ( m1_subset_1(k5_waybel_0(sK3,k4_yellow_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2385])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2746,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK3,k4_yellow_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2747,plain,
    ( m1_subset_1(k5_waybel_0(sK3,k4_yellow_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_21,plain,
    ( ~ r1_waybel_3(X0,X1,X2)
    | r2_hidden(X1,a_2_0_waybel_3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_8,plain,
    ( r1_waybel_3(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_waybel_3(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_41,negated_conjecture,
    ( v1_waybel_3(k4_yellow_0(sK3),sK3) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_624,plain,
    ( r1_waybel_3(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | k4_yellow_0(sK3) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_41])).

cnf(c_625,plain,
    ( r1_waybel_3(sK3,k4_yellow_0(sK3),k4_yellow_0(sK3))
    | ~ m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_131,plain,
    ( m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_627,plain,
    ( r1_waybel_3(sK3,k4_yellow_0(sK3),k4_yellow_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_48,c_44,c_42,c_131,c_157])).

cnf(c_903,plain,
    ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | k4_yellow_0(sK3) != X0
    | k4_yellow_0(sK3) != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_627])).

cnf(c_904,plain,
    ( r2_hidden(k4_yellow_0(sK3),a_2_0_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_903])).

cnf(c_906,plain,
    ( r2_hidden(k4_yellow_0(sK3),a_2_0_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_904,c_48,c_44,c_42,c_131,c_157])).

cnf(c_2104,plain,
    ( r2_hidden(k4_yellow_0(sK3),a_2_0_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_2114,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3127,plain,
    ( v1_xboole_0(a_2_0_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2104,c_2114])).

cnf(c_1092,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_42])).

cnf(c_1093,plain,
    ( m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1092])).

cnf(c_2096,plain,
    ( m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | a_2_0_waybel_3(X1,X0) = k1_waybel_3(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_waybel_3(X1,X0) = k1_waybel_3(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_48])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | a_2_0_waybel_3(sK3,X0) = k1_waybel_3(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_1013])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | a_2_0_waybel_3(sK3,X0) = k1_waybel_3(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_44,c_42,c_157])).

cnf(c_2099,plain,
    ( a_2_0_waybel_3(sK3,X0) = k1_waybel_3(sK3,X0)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2355,plain,
    ( a_2_0_waybel_3(sK3,k4_yellow_0(sK3)) = k1_waybel_3(sK3,k4_yellow_0(sK3)) ),
    inference(superposition,[status(thm)],[c_2096,c_2099])).

cnf(c_4952,plain,
    ( v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3127,c_2355])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_48])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_997,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_44,c_42,c_157])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k12_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1068,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k12_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_558])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k12_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_1068])).

cnf(c_1073,plain,
    ( m1_subset_1(k12_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1069,c_42])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k12_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_1073])).

cnf(c_4968,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0)))
    | v1_xboole_0(k12_waybel_0(sK3,X0)) ),
    inference(resolution,[status(thm)],[c_997,c_1074])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v1_xboole_0(k12_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_524,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0)
    | v2_yellow_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_45])).

cnf(c_525,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v24_waybel_0(sK3)
    | v2_yellow_0(sK3) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_527,plain,
    ( v2_yellow_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_525,c_48,c_45,c_44,c_43,c_42,c_154,c_157,c_162])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v1_xboole_0(k12_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_527])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v5_orders_2(sK3)
    | ~ v1_xboole_0(k12_waybel_0(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_2097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k12_waybel_0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_2100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_2626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0))) != iProver_top
    | v1_xboole_0(k12_waybel_0(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2100])).

cnf(c_2647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0)))
    | v1_xboole_0(k12_waybel_0(sK3,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2626])).

cnf(c_5516,plain,
    ( ~ v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4968,c_46,c_44,c_42,c_157,c_710,c_2647])).

cnf(c_5517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0))) ),
    inference(renaming,[status(thm)],[c_5516])).

cnf(c_4292,plain,
    ( ~ r1_xboole_0(k4_waybel_0(sK3,X0),X1)
    | ~ r2_hidden(k4_yellow_0(sK3),X1)
    | ~ v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,X0)) ),
    inference(resolution,[status(thm)],[c_31,c_643])).

cnf(c_4407,plain,
    ( ~ r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3)
    | ~ m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(resolution,[status(thm)],[c_4292,c_798])).

cnf(c_3200,plain,
    ( r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2355,c_2104])).

cnf(c_3201,plain,
    ( r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3200])).

cnf(c_3811,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_4412,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4407,c_42,c_131,c_2385,c_2746,c_3201,c_3811])).

cnf(c_17,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(k4_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_661,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(k4_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_47])).

cnf(c_662,plain,
    ( ~ v2_waybel_0(X0,sK3)
    | v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ v2_waybel_0(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_48,c_44,c_42,c_157])).

cnf(c_667,plain,
    ( ~ v2_waybel_0(X0,sK3)
    | v2_waybel_0(k4_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_666])).

cnf(c_4777,plain,
    ( ~ v2_waybel_0(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),sK3)
    | ~ m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(resolution,[status(thm)],[c_4412,c_667])).

cnf(c_19,plain,
    ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_537,plain,
    ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_44])).

cnf(c_538,plain,
    ( v2_waybel_0(k12_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( v2_waybel_0(k12_waybel_0(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_48,c_47,c_46,c_42])).

cnf(c_3813,plain,
    ( v2_waybel_0(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),sK3)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_4780,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4777,c_42,c_131,c_2385,c_2746,c_3813,c_3811])).

cnf(c_5700,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(resolution,[status(thm)],[c_5517,c_4780])).

cnf(c_5701,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5700])).

cnf(c_22912,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_55,c_132,c_2386,c_2747,c_4952,c_5701])).

cnf(c_35,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2115,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22918,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22912,c_2115])).

cnf(c_27,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_34,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_691,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_527])).

cnf(c_692,plain,
    ( r1_orders_2(sK3,X0,k4_yellow_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK3,X0,k4_yellow_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_46,c_44,c_42,c_157])).

cnf(c_697,plain,
    ( r1_orders_2(sK3,X0,k4_yellow_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_734,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | X3 != X1
    | k4_yellow_0(sK3) != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_697])).

cnf(c_735,plain,
    ( r3_orders_2(sK3,X0,k4_yellow_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k4_yellow_0(sK3),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_739,plain,
    ( r3_orders_2(sK3,X0,k4_yellow_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_48,c_44,c_42,c_131,c_157])).

cnf(c_37,negated_conjecture,
    ( ~ r3_orders_2(sK3,X0,k4_yellow_0(sK3))
    | r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_753,plain,
    ( r2_subset_1(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_739,c_37])).

cnf(c_760,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,sK4)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))) != X0
    | k1_waybel_3(sK3,k4_yellow_0(sK3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_753])).

cnf(c_761,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_1559,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_761])).

cnf(c_1612,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_1560,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_761])).

cnf(c_2108,plain,
    ( r1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_3814,plain,
    ( v2_waybel_0(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),sK3) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3813])).

cnf(c_3818,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3811])).

cnf(c_4408,plain,
    ( ~ r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | ~ v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3)
    | ~ m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))))
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3)))
    | sP0_iProver_split ),
    inference(resolution,[status(thm)],[c_4292,c_1560])).

cnf(c_4409,plain,
    ( r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3) != iProver_top
    | m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK3,k4_yellow_0(sK3))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4408])).

cnf(c_5317,plain,
    ( v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3)
    | ~ v2_waybel_0(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),sK3)
    | ~ m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_5318,plain,
    ( v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3) = iProver_top
    | v2_waybel_0(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),sK3) != iProver_top
    | m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5317])).

cnf(c_6036,plain,
    ( v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2108,c_55,c_132,c_2386,c_2747,c_3200,c_3814,c_3818,c_4409,c_4952,c_5318])).

cnf(c_5518,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5517])).

cnf(c_5855,plain,
    ( v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_5518])).

cnf(c_5856,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5855])).

cnf(c_6042,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6036,c_5856])).

cnf(c_22960,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22918,c_55,c_132,c_1612,c_2386,c_2747,c_6042])).

cnf(c_22969,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_22960])).

cnf(c_24487,plain,
    ( r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3875,c_1208,c_22969])).

cnf(c_24488,plain,
    ( r2_hidden(X0,k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24487])).

cnf(c_24497,plain,
    ( r2_hidden(k4_yellow_0(sK3),k1_waybel_3(sK3,k4_yellow_0(sK3))) != iProver_top
    | v2_waybel_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))))),sK3) != iProver_top
    | m1_subset_1(k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_24488])).

cnf(c_24969,plain,
    ( v1_xboole_0(k4_waybel_0(sK3,k12_waybel_0(sK3,k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24497,c_55,c_132,c_2386,c_2747,c_3200,c_3814,c_3818,c_5318])).

cnf(c_24974,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k5_waybel_0(sK3,k4_yellow_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24969,c_5856])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24974,c_2747,c_2386,c_132,c_55])).


%------------------------------------------------------------------------------
