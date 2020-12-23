%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:07 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  285 (2025 expanded)
%              Number of clauses        :  166 ( 500 expanded)
%              Number of leaves         :   30 ( 502 expanded)
%              Depth                    :   27
%              Number of atoms          : 1401 (21644 expanded)
%              Number of equality atoms :  398 (2775 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f76])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f77])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK10),X1)
        & k1_xboole_0 != sK10
        & m1_subset_1(sK10,k1_zfmisc_1(X1))
        & v1_finset_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ? [X2] :
              ( ~ r2_hidden(k1_yellow_0(X0,X2),sK9)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(sK9))
              & v1_finset_1(X2) )
          | ~ v1_waybel_0(sK9,X0) )
        & ( ! [X3] :
              ( r2_hidden(k1_yellow_0(X0,X3),sK9)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
              | ~ v1_finset_1(X3) )
          | v1_waybel_0(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK9,X0)
        & ~ v1_xboole_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
              | ~ v1_waybel_0(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(sK8,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,sK8) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(sK8,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & v12_waybel_0(X1,sK8)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK8)
      & v1_lattice3(sK8)
      & v5_orders_2(sK8)
      & v4_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,
    ( ( ( ~ r2_hidden(k1_yellow_0(sK8,sK10),sK9)
        & k1_xboole_0 != sK10
        & m1_subset_1(sK10,k1_zfmisc_1(sK9))
        & v1_finset_1(sK10) )
      | ~ v1_waybel_0(sK9,sK8) )
    & ( ! [X3] :
          ( r2_hidden(k1_yellow_0(sK8,X3),sK9)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
          | ~ v1_finset_1(X3) )
      | v1_waybel_0(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v12_waybel_0(sK9,sK8)
    & ~ v1_xboole_0(sK9)
    & l1_orders_2(sK8)
    & v1_lattice3(sK8)
    & v5_orders_2(sK8)
    & v4_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f78,f81,f80,f79])).

fof(f134,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f82])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f130,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f131,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f132,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f82])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f127,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f128,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f129,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f133,plain,(
    v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r2_lattice3(X0,X2,X3)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r2_lattice3(X0,X2,X3)
                & r2_hidden(X3,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X2) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r2_lattice3(X0,X4,X5)
                & r2_hidden(X5,X1)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f67,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r2_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X4,sK5(X0,X1,X4))
        & r2_hidden(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r2_lattice3(X0,sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r2_lattice3(X0,sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
          & v1_finset_1(sK4(X0,X1)) ) )
      & ( ! [X4] :
            ( ( r2_lattice3(X0,X4,sK5(X0,X1,X4))
              & r2_hidden(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f104,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( r1_yellow_0(X0,X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X1)
              | v1_xboole_0(X1) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f72])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r1_yellow_0(X0,sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK7(X0))
        & ~ v1_xboole_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,sK7(X0))
            & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK7(X0))
            & ~ v1_xboole_0(sK7(X0)) ) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).

fof(f120,plain,(
    ! [X2,X0] :
      ( r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f103,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v1_finset_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f135,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK8,X3),sK9)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
      | ~ v1_finset_1(X3)
      | v1_waybel_0(sK9,sK8) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f12,axiom,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f12])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK6(X0,X1,X2))
        & r2_lattice3(X0,X2,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK6(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f69])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f141,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_lattice3(X0,sK4(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f53,f52])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ( ( ( v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ( ( ( v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( ( v1_waybel_0(X0,X1)
            & ~ v1_xboole_0(X0) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1)
          | v1_xboole_0(X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f62])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_lattice3(X0,X4,sK5(X0,X1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f140,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f110])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,X2)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK3(X0,X1),X2)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
            & r1_orders_2(X0,X3,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f139,plain,
    ( ~ r2_hidden(k1_yellow_0(sK8,sK10),sK9)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f136,plain,
    ( v1_finset_1(sK10)
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f137,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9))
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f138,plain,
    ( k1_xboole_0 != sK10
    | ~ v1_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10,plain,
    ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v12_waybel_0(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1947,plain,
    ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v12_waybel_0(X1,X0) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1911,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_13,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1944,plain,
    ( m2_subset_1(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6508,plain,
    ( m2_subset_1(X0,u1_struct_0(sK8),sK9) != iProver_top
    | m1_subset_1(X0,sK9) = iProver_top
    | v1_xboole_0(u1_struct_0(sK8)) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1944])).

cnf(c_53,negated_conjecture,
    ( v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_60,plain,
    ( v1_lattice3(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_61,plain,
    ( l1_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_62,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_158,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_160,plain,
    ( v1_xboole_0(u1_struct_0(sK8)) != iProver_top
    | l1_struct_0(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_165,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_167,plain,
    ( l1_struct_0(sK8) = iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_187,plain,
    ( l1_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top
    | v2_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_189,plain,
    ( l1_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_6925,plain,
    ( m2_subset_1(X0,u1_struct_0(sK8),sK9) != iProver_top
    | m1_subset_1(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6508,c_60,c_61,c_62,c_160,c_167,c_189])).

cnf(c_8034,plain,
    ( m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | v3_orders_2(sK8) != iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top
    | l1_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1947,c_6925])).

cnf(c_56,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_57,plain,
    ( v3_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_58,plain,
    ( v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_54,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_59,plain,
    ( v5_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_50,negated_conjecture,
    ( v12_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_63,plain,
    ( v12_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_64,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_2745,plain,
    ( m2_subset_1(o_2_7_waybel_0(sK8,sK9),u1_struct_0(sK8),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v12_waybel_0(sK9,sK8)
    | ~ v3_orders_2(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v5_orders_2(sK8)
    | v1_xboole_0(sK9)
    | ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2746,plain,
    ( m2_subset_1(o_2_7_waybel_0(sK8,sK9),u1_struct_0(sK8),sK9) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | v3_orders_2(sK8) != iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top
    | l1_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2745])).

cnf(c_2862,plain,
    ( ~ m2_subset_1(o_2_7_waybel_0(sK8,sK9),u1_struct_0(sK8),sK9)
    | m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(u1_struct_0(sK8))
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2866,plain,
    ( m2_subset_1(o_2_7_waybel_0(sK8,sK9),u1_struct_0(sK8),sK9) != iProver_top
    | m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK8)) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_8434,plain,
    ( m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8034,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_160,c_167,c_189,c_2746,c_2866])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1932,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8439,plain,
    ( r2_hidden(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8434,c_1932])).

cnf(c_2972,plain,
    ( ~ m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9)
    | r2_hidden(o_2_7_waybel_0(sK8,sK9),sK9)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2973,plain,
    ( m1_subset_1(o_2_7_waybel_0(sK8,sK9),sK9) != iProver_top
    | r2_hidden(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2972])).

cnf(c_8732,plain,
    ( r2_hidden(o_2_7_waybel_0(sK8,sK9),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8439,c_57,c_58,c_59,c_60,c_61,c_62,c_63,c_64,c_160,c_167,c_189,c_2746,c_2866,c_2973])).

cnf(c_18,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1939,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_35,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1924,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3219,plain,
    ( r1_tarski(sK4(X0,X1),X1) = iProver_top
    | sP0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1939,c_1924])).

cnf(c_2914,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1924])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1933,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3593,plain,
    ( r1_tarski(X0,u1_struct_0(sK8)) = iProver_top
    | r1_tarski(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2914,c_1933])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1925,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_41,plain,
    ( r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_596,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41,c_0])).

cnf(c_597,plain,
    ( r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_596])).

cnf(c_1902,plain,
    ( r1_yellow_0(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_finset_1(X1) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_3192,plain,
    ( r1_yellow_0(X0,X1) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v1_finset_1(X1) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_1902])).

cnf(c_10010,plain,
    ( r1_yellow_0(sK8,X0) = iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v3_orders_2(sK8) != iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | l1_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3593,c_3192])).

cnf(c_11303,plain,
    ( v1_finset_1(X0) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | r1_yellow_0(sK8,X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10010,c_57,c_58,c_59,c_60,c_61])).

cnf(c_11304,plain,
    ( r1_yellow_0(sK8,X0) = iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11303])).

cnf(c_11313,plain,
    ( r1_yellow_0(sK8,sK4(X0,sK9)) = iProver_top
    | sP0(X0,sK9) = iProver_top
    | v1_finset_1(sK4(X0,sK9)) != iProver_top
    | v1_xboole_0(sK4(X0,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3219,c_11304])).

cnf(c_19,plain,
    ( sP0(X0,X1)
    | v1_finset_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4996,plain,
    ( sP0(X0,sK9)
    | v1_finset_1(sK4(X0,sK9)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4997,plain,
    ( sP0(X0,sK9) = iProver_top
    | v1_finset_1(sK4(X0,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4996])).

cnf(c_12857,plain,
    ( sP0(X0,sK9) = iProver_top
    | r1_yellow_0(sK8,sK4(X0,sK9)) = iProver_top
    | v1_xboole_0(sK4(X0,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11313,c_4997])).

cnf(c_12858,plain,
    ( r1_yellow_0(sK8,sK4(X0,sK9)) = iProver_top
    | sP0(X0,sK9) = iProver_top
    | v1_xboole_0(sK4(X0,sK9)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12857])).

cnf(c_48,negated_conjecture,
    ( v1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
    | r2_hidden(k1_yellow_0(sK8,X0),sK9)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1912,plain,
    ( k1_xboole_0 = X0
    | v1_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_33,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_7,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_575,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_7])).

cnf(c_576,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_575])).

cnf(c_1903,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,sK4(X0,X1),X2)
    | sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1940,plain,
    ( r2_lattice3(X0,sK4(X0,X1),X2) != iProver_top
    | sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5847,plain,
    ( r1_yellow_0(X0,sK4(X0,X1)) != iProver_top
    | sP0(X0,X1) = iProver_top
    | m1_subset_1(k1_yellow_0(X0,sK4(X0,X1)),u1_struct_0(X0)) != iProver_top
    | r2_hidden(k1_yellow_0(X0,sK4(X0,X1)),X1) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1903,c_1940])).

cnf(c_1950,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6087,plain,
    ( r1_yellow_0(X0,sK4(X0,X1)) != iProver_top
    | sP0(X0,X1) = iProver_top
    | r2_hidden(k1_yellow_0(X0,sK4(X0,X1)),X1) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5847,c_1950])).

cnf(c_6091,plain,
    ( sK4(sK8,sK9) = k1_xboole_0
    | r1_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | v1_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) != iProver_top
    | v1_finset_1(sK4(sK8,sK9)) != iProver_top
    | v5_orders_2(sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1912,c_6087])).

cnf(c_23,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2633,plain,
    ( sP1(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v4_orders_2(sK8)
    | ~ l1_orders_2(sK8)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2634,plain,
    ( sP1(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v4_orders_2(sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2633])).

cnf(c_14,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2858,plain,
    ( ~ sP1(sK9,sK8)
    | ~ sP0(sK8,sK9)
    | v1_waybel_0(sK9,sK8) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2859,plain,
    ( sP1(sK9,sK8) != iProver_top
    | sP0(sK8,sK9) != iProver_top
    | v1_waybel_0(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2858])).

cnf(c_2966,plain,
    ( sP0(sK8,sK9)
    | v1_finset_1(sK4(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2967,plain,
    ( sP0(sK8,sK9) = iProver_top
    | v1_finset_1(sK4(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2966])).

cnf(c_2965,plain,
    ( sP0(sK8,sK9)
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2969,plain,
    ( sP0(sK8,sK9) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2965])).

cnf(c_6144,plain,
    ( r1_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | sK4(sK8,sK9) = k1_xboole_0
    | v1_waybel_0(sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6091,c_58,c_59,c_60,c_61,c_64,c_189,c_2634,c_2859,c_2967,c_2969])).

cnf(c_6145,plain,
    ( sK4(sK8,sK9) = k1_xboole_0
    | r1_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | v1_waybel_0(sK9,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_6144])).

cnf(c_12866,plain,
    ( sK4(sK8,sK9) = k1_xboole_0
    | sP0(sK8,sK9) = iProver_top
    | v1_waybel_0(sK9,sK8) = iProver_top
    | v1_xboole_0(sK4(sK8,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12858,c_6145])).

cnf(c_188,plain,
    ( ~ l1_orders_2(sK8)
    | ~ v1_lattice3(sK8)
    | ~ v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_42,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4784,plain,
    ( ~ v1_xboole_0(sK4(sK8,sK9))
    | k1_xboole_0 = sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_640,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3078,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_4630,plain,
    ( X0 != sK4(sK8,sK9)
    | X0 = k1_xboole_0
    | k1_xboole_0 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_5092,plain,
    ( sK4(sK8,sK9) != sK4(sK8,sK9)
    | sK4(sK8,sK9) = k1_xboole_0
    | k1_xboole_0 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4630])).

cnf(c_639,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5093,plain,
    ( sK4(sK8,sK9) = sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ v1_finset_1(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1936,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,X2),X1) = iProver_top
    | v1_finset_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( r2_lattice3(X0,X1,sK5(X0,X2,X1))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_finset_1(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1937,plain,
    ( r2_lattice3(X0,X1,sK5(X0,X2,X1)) = iProver_top
    | sP0(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_32,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_7])).

cnf(c_606,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_605])).

cnf(c_1901,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1951,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,X3) = iProver_top
    | v12_waybel_0(X3,X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_36,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1923,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2370,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(X1,X3) = iProver_top
    | v12_waybel_0(X3,X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1951,c_1923])).

cnf(c_8950,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top
    | v12_waybel_0(sK9,sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_2370])).

cnf(c_9370,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(X0,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8950,c_61,c_63])).

cnf(c_9380,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,X0),X1) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_9370])).

cnf(c_9630,plain,
    ( r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r1_orders_2(sK8,k1_yellow_0(sK8,X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9380,c_61])).

cnf(c_9631,plain,
    ( r1_orders_2(sK8,k1_yellow_0(sK8,X0),X1) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_9630])).

cnf(c_9639,plain,
    ( r2_lattice3(sK8,X0,X1) != iProver_top
    | r1_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | v5_orders_2(sK8) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_9631])).

cnf(c_10434,plain,
    ( r2_lattice3(sK8,X0,X1) != iProver_top
    | r1_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9639,c_59,c_61])).

cnf(c_4028,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_1923])).

cnf(c_10445,plain,
    ( r2_lattice3(sK8,X0,X1) != iProver_top
    | r1_yellow_0(sK8,X0) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10434,c_4028])).

cnf(c_10449,plain,
    ( r1_yellow_0(sK8,X0) != iProver_top
    | sP0(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK5(sK8,X1,X0),sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_10445])).

cnf(c_10682,plain,
    ( r1_yellow_0(sK8,X0) != iProver_top
    | sP0(sK8,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_10449])).

cnf(c_44,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | ~ r2_hidden(k1_yellow_0(sK8,sK10),sK9) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1916,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(k1_yellow_0(sK8,sK10),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11564,plain,
    ( r1_yellow_0(sK8,sK10) != iProver_top
    | sP0(sK8,sK9) != iProver_top
    | v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
    | v1_finset_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_10682,c_1916])).

cnf(c_47,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | v1_finset_1(sK10) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_68,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | v1_finset_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_69,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( ~ v1_waybel_0(sK9,sK8)
    | k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_70,plain,
    ( k1_xboole_0 != sK10
    | v1_waybel_0(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_2571,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2572,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2571])).

cnf(c_1914,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_2913,plain,
    ( r1_tarski(sK10,sK9) = iProver_top
    | v1_waybel_0(sK9,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1924])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v1_waybel_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2962,plain,
    ( ~ sP1(sK9,sK8)
    | sP0(sK8,sK9)
    | ~ v1_waybel_0(sK9,sK8)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2963,plain,
    ( sP1(sK9,sK8) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | v1_waybel_0(sK9,sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2962])).

cnf(c_3327,plain,
    ( r1_yellow_0(X0,sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(sK10)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(sK10)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_3333,plain,
    ( r1_yellow_0(X0,sK10) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v1_finset_1(sK10) != iProver_top
    | v3_orders_2(X0) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v5_orders_2(X0) != iProver_top
    | v1_xboole_0(sK10) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | v1_lattice3(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3327])).

cnf(c_3335,plain,
    ( r1_yellow_0(sK8,sK10) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_finset_1(sK10) != iProver_top
    | v3_orders_2(sK8) != iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v5_orders_2(sK8) != iProver_top
    | v1_xboole_0(sK10) = iProver_top
    | l1_orders_2(sK8) != iProver_top
    | v1_lattice3(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3333])).

cnf(c_3856,plain,
    ( ~ v1_xboole_0(sK10)
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_3857,plain,
    ( k1_xboole_0 = sK10
    | v1_xboole_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3856])).

cnf(c_3789,plain,
    ( ~ r1_tarski(sK9,X0)
    | r1_tarski(sK10,X0)
    | ~ r1_tarski(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5086,plain,
    ( ~ r1_tarski(sK9,u1_struct_0(sK8))
    | r1_tarski(sK10,u1_struct_0(sK8))
    | ~ r1_tarski(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_3789])).

cnf(c_5087,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(sK10,u1_struct_0(sK8)) = iProver_top
    | r1_tarski(sK10,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5086])).

cnf(c_6432,plain,
    ( ~ r1_tarski(sK10,u1_struct_0(sK8))
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_6433,plain,
    ( r1_tarski(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6432])).

cnf(c_11680,plain,
    ( v1_waybel_0(sK9,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11564,c_57,c_58,c_59,c_60,c_61,c_62,c_64,c_68,c_69,c_70,c_189,c_2572,c_2634,c_2913,c_2963,c_3335,c_3857,c_5087,c_6433])).

cnf(c_11682,plain,
    ( ~ v1_waybel_0(sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11680])).

cnf(c_12867,plain,
    ( sP0(sK8,sK9)
    | v1_waybel_0(sK9,sK8)
    | v1_xboole_0(sK4(sK8,sK9))
    | sK4(sK8,sK9) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12866])).

cnf(c_12869,plain,
    ( sK4(sK8,sK9) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12866,c_55,c_53,c_52,c_49,c_188,c_2633,c_2858,c_4784,c_5092,c_5093,c_11682,c_12867])).

cnf(c_12877,plain,
    ( r2_lattice3(sK8,k1_xboole_0,X0) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_12869,c_1940])).

cnf(c_3494,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_36,c_49])).

cnf(c_3495,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3494])).

cnf(c_43,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1917,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4160,plain,
    ( r2_lattice3(sK8,k1_xboole_0,X0) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | l1_orders_2(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_1917])).

cnf(c_13134,plain,
    ( r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12877,c_57,c_58,c_59,c_60,c_61,c_62,c_64,c_68,c_69,c_70,c_189,c_2572,c_2634,c_2859,c_2913,c_2963,c_3335,c_3495,c_3857,c_4160,c_5087,c_6433,c_11564])).

cnf(c_13145,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_8732,c_13134])).


%------------------------------------------------------------------------------
