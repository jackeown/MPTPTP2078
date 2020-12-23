%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1992+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:00 EST 2020

% Result     : Theorem 46.72s
% Output     : CNFRefutation 46.72s
% Verified   : 
% Statistics : Number of formulae       :  315 (3469 expanded)
%              Number of clauses        :  179 ( 826 expanded)
%              Number of leaves         :   35 ( 828 expanded)
%              Depth                    :   33
%              Number of atoms          : 1386 (34212 expanded)
%              Number of equality atoms :  198 ( 406 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   30 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f90,f91])).

fof(f129,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f82])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f83])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f74])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f29,conjecture,(
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

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f32,plain,(
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
    inference(pure_predicate_removal,[],[f30])).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f80,plain,(
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
    inference(flattening,[],[f79])).

fof(f96,plain,(
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
            | ~ r2_hidden(X2,sK5)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r1_waybel_3(X0,k2_yellow_0(X0,sK5),k4_yellow_0(X0))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,
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
   => ( ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(sK4,X2,k4_yellow_0(sK4))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
            & r1_waybel_3(sK4,k2_yellow_0(sK4,X1),k4_yellow_0(sK4))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(sK4),sK4)
      & l1_orders_2(sK4)
      & v3_waybel_3(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,
    ( ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
      | ( ! [X2] :
            ( ~ r3_orders_2(sK4,X2,k4_yellow_0(sK4))
            | ~ r2_hidden(X2,sK5)
            | ~ m1_subset_1(X2,u1_struct_0(sK4)) )
        & r1_waybel_3(sK4,k2_yellow_0(sK4,sK5),k4_yellow_0(sK4))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
        & ~ v1_xboole_0(sK5) ) )
    & v1_waybel_3(k4_yellow_0(sK4),sK4)
    & l1_orders_2(sK4)
    & v3_waybel_3(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f80,f96,f95])).

fof(f145,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f143,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f139,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f140,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f141,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
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

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f85,plain,(
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
    inference(rectify,[],[f84])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_waybel_3(X1,sK1(X0,X1,X2),X2)
        & sK1(X0,X1,X2) = X0
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f85,f86])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      | ~ r1_waybel_3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f151,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_waybel_3(X1,X2))
      | ~ r1_waybel_3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f123])).

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

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_waybel_3(X0,X1,X1)
      | ~ v1_waybel_3(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f146,plain,(
    v1_waybel_3(k4_yellow_0(sK4),sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
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

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f128,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f142,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f97])).

fof(f144,plain,(
    v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f97])).

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

fof(f33,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0] :
      ( ( v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f104,plain,(
    ! [X0] :
      ( v24_waybel_0(X0)
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f34,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f100,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( ( r2_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r2_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f147,plain,
    ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f97])).

fof(f23,axiom,(
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

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f71,f93])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f148,plain,
    ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f97])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f89,plain,(
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
    inference(nnf_transformation,[],[f67])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f150,plain,(
    ! [X2] :
      ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
      | ~ r3_orders_2(sK4,X2,k4_yellow_0(sK4))
      | ~ r2_hidden(X2,sK5)
      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_15,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2252,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_32,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2249,plain,
    ( X0 = X1
    | r2_hidden(sK2(X1,X0),X0) = iProver_top
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2251,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2245,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2781,plain,
    ( r2_hidden(X0,sK0(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_2245])).

cnf(c_3523,plain,
    ( sK0(k1_zfmisc_1(X0)) = X1
    | r2_hidden(sK2(sK0(k1_zfmisc_1(X0)),X1),X1) = iProver_top
    | m1_subset_1(sK2(sK0(k1_zfmisc_1(X0)),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_2781])).

cnf(c_38,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2244,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_11265,plain,
    ( sK0(k1_zfmisc_1(k1_zfmisc_1(X0))) = X1
    | r2_hidden(X2,sK2(sK0(k1_zfmisc_1(k1_zfmisc_1(X0))),X1)) != iProver_top
    | r2_hidden(sK2(sK0(k1_zfmisc_1(k1_zfmisc_1(X0))),X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3523,c_2244])).

cnf(c_31381,plain,
    ( sK2(sK0(k1_zfmisc_1(k1_zfmisc_1(X0))),X1) = X2
    | sK0(k1_zfmisc_1(k1_zfmisc_1(X0))) = X1
    | r2_hidden(sK2(X2,sK2(sK0(k1_zfmisc_1(k1_zfmisc_1(X0))),X1)),X2) = iProver_top
    | r2_hidden(sK2(sK0(k1_zfmisc_1(k1_zfmisc_1(X0))),X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_11265])).

cnf(c_46,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_59,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_13,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_142,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_144,plain,
    ( m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3,plain,
    ( ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_48,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_596,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_48])).

cnf(c_597,plain,
    ( ~ v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_169,plain,
    ( ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_599,plain,
    ( ~ v2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_48,c_46,c_169])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_599])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_1091])).

cnf(c_1096,plain,
    ( m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1092,c_46])).

cnf(c_1097,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1096])).

cnf(c_2379,plain,
    ( m1_subset_1(k5_waybel_0(sK4,k4_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_2380,plain,
    ( m1_subset_1(k5_waybel_0(sK4,k4_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_1640,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2436,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_2437,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2692,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK4,k4_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2693,plain,
    ( m1_subset_1(k5_waybel_0(sK4,k4_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2692])).

cnf(c_20,plain,
    ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_578,plain,
    ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_48])).

cnf(c_579,plain,
    ( v2_waybel_0(k12_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_52,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_51,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_50,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_583,plain,
    ( v2_waybel_0(k12_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_52,c_51,c_50,c_46])).

cnf(c_3662,plain,
    ( v2_waybel_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),sK4)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_3663,plain,
    ( v2_waybel_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),sK4) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3662])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k12_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k12_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_599])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k12_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_1114,plain,
    ( m1_subset_1(k12_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_46])).

cnf(c_1115,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k12_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1114])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_3667,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_18,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(k4_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_702,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(k4_waybel_0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_51])).

cnf(c_703,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_702])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ v2_waybel_0(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_703,c_52,c_48,c_46,c_169])).

cnf(c_708,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_707])).

cnf(c_6212,plain,
    ( v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4)
    | ~ v2_waybel_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),sK4)
    | ~ m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_6222,plain,
    ( v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4) = iProver_top
    | v2_waybel_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),sK4) != iProver_top
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6212])).

cnf(c_1133,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_46])).

cnf(c_1134,plain,
    ( m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1133])).

cnf(c_2224,plain,
    ( m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | a_2_0_waybel_3(X1,X0) = k1_waybel_3(X1,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | a_2_0_waybel_3(X1,X0) = k1_waybel_3(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_52])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | a_2_0_waybel_3(sK4,X0) = k1_waybel_3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_1059,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | a_2_0_waybel_3(sK4,X0) = k1_waybel_3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1055,c_48,c_46,c_169])).

cnf(c_2227,plain,
    ( a_2_0_waybel_3(sK4,X0) = k1_waybel_3(sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_3261,plain,
    ( a_2_0_waybel_3(sK4,k4_yellow_0(sK4)) = k1_waybel_3(sK4,k4_yellow_0(sK4)) ),
    inference(superposition,[status(thm)],[c_2224,c_2227])).

cnf(c_22,plain,
    ( ~ r1_waybel_3(X0,X1,X2)
    | r2_hidden(X1,a_2_0_waybel_3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_8,plain,
    ( r1_waybel_3(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_waybel_3(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_45,negated_conjecture,
    ( v1_waybel_3(k4_yellow_0(sK4),sK4) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_665,plain,
    ( r1_waybel_3(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | k4_yellow_0(sK4) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_45])).

cnf(c_666,plain,
    ( r1_waybel_3(sK4,k4_yellow_0(sK4),k4_yellow_0(sK4))
    | ~ m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_143,plain,
    ( m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_668,plain,
    ( r1_waybel_3(sK4,k4_yellow_0(sK4),k4_yellow_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_52,c_48,c_46,c_143,c_169])).

cnf(c_944,plain,
    ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | k4_yellow_0(sK4) != X0
    | k4_yellow_0(sK4) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_668])).

cnf(c_945,plain,
    ( r2_hidden(k4_yellow_0(sK4),a_2_0_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_947,plain,
    ( r2_hidden(k4_yellow_0(sK4),a_2_0_waybel_3(sK4,k4_yellow_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_52,c_48,c_46,c_143,c_169])).

cnf(c_2232,plain,
    ( r2_hidden(k4_yellow_0(sK4),a_2_0_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_12125,plain,
    ( r2_hidden(k4_yellow_0(sK4),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_2232])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_52])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k4_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1034,c_48,c_46,c_169])).

cnf(c_18670,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | v1_xboole_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_18671,plain,
    ( m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | v1_xboole_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18670])).

cnf(c_17,plain,
    ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_30,plain,
    ( r2_hidden(k4_yellow_0(X0),X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ v13_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_612,plain,
    ( r2_hidden(k4_yellow_0(X0),X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X3)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | X0 != X3
    | k4_waybel_0(X3,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_613,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_639,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_613,c_12])).

cnf(c_678,plain,
    ( r2_hidden(k4_yellow_0(X0),k4_waybel_0(X0,X1))
    | ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | v1_xboole_0(k4_waybel_0(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_639,c_51])).

cnf(c_679,plain,
    ( r2_hidden(k4_yellow_0(sK4),k4_waybel_0(sK4,X0))
    | ~ v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v5_orders_2(sK4)
    | v1_xboole_0(k4_waybel_0(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v2_yellow_0(sK4) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_49,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_47,negated_conjecture,
    ( v3_waybel_3(sK4) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_4,plain,
    ( ~ v3_waybel_3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v24_waybel_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_166,plain,
    ( ~ v3_waybel_3(sK4)
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v24_waybel_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v24_waybel_0(X0)
    | v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_174,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v24_waybel_0(sK4)
    | v2_yellow_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | r2_hidden(k4_yellow_0(sK4),k4_waybel_0(sK4,X0))
    | v1_xboole_0(k4_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_52,c_50,c_49,c_48,c_47,c_46,c_166,c_169,c_174])).

cnf(c_684,plain,
    ( r2_hidden(k4_yellow_0(sK4),k4_waybel_0(sK4,X0))
    | ~ v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,X0)) ),
    inference(renaming,[status(thm)],[c_683])).

cnf(c_2240,plain,
    ( r2_hidden(k4_yellow_0(sK4),k4_waybel_0(sK4,X0)) = iProver_top
    | v2_waybel_0(k4_waybel_0(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_27,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r2_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_44,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_822,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK5)
    | k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) != X0
    | k1_waybel_3(sK4,k4_yellow_0(sK4)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_44])).

cnf(c_823,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_822])).

cnf(c_2235,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_34,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3272,plain,
    ( r1_xboole_0(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_34,c_40])).

cnf(c_4242,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | ~ v1_xboole_0(sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3272,c_823])).

cnf(c_35,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3280,plain,
    ( r1_xboole_0(X0,X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_35,c_40])).

cnf(c_4718,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ v1_xboole_0(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4242,c_3280])).

cnf(c_4719,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4718])).

cnf(c_7615,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2235,c_4719])).

cnf(c_33,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2248,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7619,plain,
    ( r2_hidden(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7615,c_2248])).

cnf(c_19664,plain,
    ( r2_hidden(k4_yellow_0(sK4),k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4) != iProver_top
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_7619])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v1_xboole_0(k12_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_yellow_0(X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_565,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v24_waybel_0(X0)
    | v2_yellow_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_49])).

cnf(c_566,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v24_waybel_0(sK4)
    | v2_yellow_0(sK4) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( v2_yellow_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_52,c_49,c_48,c_47,c_46,c_166,c_169,c_174])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v5_orders_2(X1)
    | ~ v1_xboole_0(k12_waybel_0(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_568])).

cnf(c_751,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v5_orders_2(sK4)
    | ~ v1_xboole_0(k12_waybel_0(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(k12_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_751,c_50,c_48,c_46,c_169])).

cnf(c_60404,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_60405,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60404])).

cnf(c_2242,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2559,plain,
    ( X0 = X1
    | r2_hidden(sK2(X0,X1),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2249,c_2242])).

cnf(c_2247,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,negated_conjecture,
    ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_838,plain,
    ( r1_xboole_0(X0,X1)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) != X0
    | k1_waybel_3(sK4,k4_yellow_0(sK4)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_43])).

cnf(c_839,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_2234,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_4240,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3272,c_839])).

cnf(c_5211,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4240,c_3280])).

cnf(c_5212,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5211])).

cnf(c_6145,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_5212])).

cnf(c_6149,plain,
    ( r2_hidden(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6145,c_2248])).

cnf(c_24348,plain,
    ( r1_xboole_0(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | r2_hidden(sK3(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_6149])).

cnf(c_4741,plain,
    ( ~ r1_xboole_0(k4_waybel_0(sK4,X0),X1)
    | ~ r2_hidden(k4_yellow_0(sK4),X1)
    | ~ v2_waybel_0(k4_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_33,c_684])).

cnf(c_5634,plain,
    ( ~ r2_hidden(k4_yellow_0(sK4),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4)
    | ~ m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) ),
    inference(resolution,[status(thm)],[c_5211,c_4741])).

cnf(c_5635,plain,
    ( r2_hidden(k4_yellow_0(sK4),k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4) != iProver_top
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5634])).

cnf(c_118567,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24348,c_59,c_144,c_2380,c_2693,c_3663,c_3667,c_5635,c_6222,c_12125,c_18671,c_60405])).

cnf(c_118590,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_118567,c_2245])).

cnf(c_28,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_36,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_732,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_568])).

cnf(c_733,plain,
    ( r1_orders_2(sK4,X0,k4_yellow_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v5_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_orders_2(sK4,X0,k4_yellow_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_50,c_48,c_46,c_169])).

cnf(c_738,plain,
    ( r1_orders_2(sK4,X0,k4_yellow_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_775,plain,
    ( r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | X3 != X1
    | k4_yellow_0(sK4) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_738])).

cnf(c_776,plain,
    ( r3_orders_2(sK4,X0,k4_yellow_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k4_yellow_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_780,plain,
    ( r3_orders_2(sK4,X0,k4_yellow_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_52,c_48,c_46,c_143,c_169])).

cnf(c_41,negated_conjecture,
    ( ~ r3_orders_2(sK4,X0,k4_yellow_0(sK4))
    | r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_794,plain,
    ( r2_subset_1(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_780,c_41])).

cnf(c_801,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,sK5)
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))) != X0
    | k1_waybel_3(sK4,k4_yellow_0(sK4)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_794])).

cnf(c_802,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_1625,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_802])).

cnf(c_1678,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_1626,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_802])).

cnf(c_2236,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | v1_xboole_0(k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_4241,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4)))
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))))
    | sP0_iProver_split ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3272,c_1626])).

cnf(c_4246,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4241])).

cnf(c_7845,plain,
    ( v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2236,c_4246])).

cnf(c_7846,plain,
    ( r1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),k1_waybel_3(sK4,k4_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_7845])).

cnf(c_7849,plain,
    ( r2_hidden(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_7846,c_2248])).

cnf(c_67676,plain,
    ( r2_hidden(X0,k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7849,c_59,c_144,c_2380,c_2693,c_3667,c_18671,c_60405])).

cnf(c_67677,plain,
    ( r2_hidden(X0,k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) != iProver_top
    | r2_hidden(X0,k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_67676])).

cnf(c_67688,plain,
    ( r2_hidden(k4_yellow_0(sK4),k1_waybel_3(sK4,k4_yellow_0(sK4))) != iProver_top
    | v2_waybel_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4))))),sK4) != iProver_top
    | m1_subset_1(k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k4_waybel_0(sK4,k12_waybel_0(sK4,k3_subset_1(u1_struct_0(sK4),k5_waybel_0(sK4,k4_yellow_0(sK4)))))) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_67677])).

cnf(c_119187,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_118590,c_59,c_144,c_1678,c_2380,c_2693,c_3663,c_3667,c_6222,c_12125,c_18671,c_60405,c_67688])).

cnf(c_119193,plain,
    ( sK5 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_119187])).

cnf(c_123523,plain,
    ( v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31381,c_59,c_144,c_2380,c_2437,c_2693,c_3663,c_3667,c_6222,c_12125,c_18671,c_19664,c_60405,c_119193])).

cnf(c_123529,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2252,c_123523])).


%------------------------------------------------------------------------------
