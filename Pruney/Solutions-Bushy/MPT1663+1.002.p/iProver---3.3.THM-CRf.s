%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1663+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  289 (3809 expanded)
%              Number of clauses        :  182 ( 864 expanded)
%              Number of leaves         :   28 ( 975 expanded)
%              Depth                    :   31
%              Number of atoms          : 1332 (42549 expanded)
%              Number of equality atoms :  306 (4778 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f47])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_lattice3(X0,X2,X3)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_lattice3(X0,X2,X3)
                & r2_hidden(X3,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X2) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_lattice3(X0,X4,X5)
                & r2_hidden(X5,X1)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,X4,sK6(X0,X1,X4))
        & r2_hidden(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r1_lattice3(X0,sK5(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_lattice3(X0,sK5(X0,X1),X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1))
          & v1_finset_1(sK5(X0,X1)) ) )
      & ( ! [X4] :
            ( ( r1_lattice3(X0,X4,sK6(X0,X1,X4))
              & r2_hidden(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f55,f54])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK11),X1)
        & k1_xboole_0 != sK11
        & m1_subset_1(sK11,k1_zfmisc_1(X1))
        & v1_finset_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ? [X2] :
              ( ~ r2_hidden(k2_yellow_0(X0,X2),sK10)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(sK10))
              & v1_finset_1(X2) )
          | ~ v2_waybel_0(sK10,X0) )
        & ( ! [X3] :
              ( r2_hidden(k2_yellow_0(X0,X3),sK10)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
              | ~ v1_finset_1(X3) )
          | v2_waybel_0(sK10,X0) )
        & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK10,X0)
        & ~ v1_xboole_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | v2_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(sK9,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,sK9) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(sK9,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,sK9) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))
          & v13_waybel_0(X1,sK9)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK9)
      & v2_lattice3(sK9)
      & v5_orders_2(sK9)
      & v4_orders_2(sK9)
      & v3_orders_2(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( ( ~ r2_hidden(k2_yellow_0(sK9,sK11),sK10)
        & k1_xboole_0 != sK11
        & m1_subset_1(sK11,k1_zfmisc_1(sK10))
        & v1_finset_1(sK11) )
      | ~ v2_waybel_0(sK10,sK9) )
    & ( ! [X3] :
          ( r2_hidden(k2_yellow_0(sK9,X3),sK10)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
          | ~ v1_finset_1(X3) )
      | v2_waybel_0(sK10,sK9) )
    & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    & v13_waybel_0(sK10,sK9)
    & ~ v1_xboole_0(sK10)
    & l1_orders_2(sK9)
    & v2_lattice3(sK9)
    & v5_orders_2(sK9)
    & v4_orders_2(sK9)
    & v3_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f66,f69,f68,f67])).

fof(f117,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( r2_yellow_0(X0,X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X1)
              | v1_xboole_0(X1) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r2_yellow_0(X0,sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,sK8(X0))
            & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK8(X0))
            & ~ v1_xboole_0(sK8(X0)) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f61,f62])).

fof(f103,plain,(
    ! [X2,X0] :
      ( r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,(
    v3_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f111,plain,(
    v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f112,plain,(
    v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f113,plain,(
    v2_lattice3(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f114,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v1_finset_1(sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK9,X3),sK10)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK10,sK9) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f57])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f124,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r1_lattice3(X0,sK5(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ( ( ( v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ( ( ( v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( ( v2_waybel_0(X0,X1)
            & ~ v1_xboole_0(X0) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_waybel_0(X0,X1)
          | v1_xboole_0(X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f40,f39])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,
    ( k1_xboole_0 != sK11
    | ~ v2_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f70])).

fof(f119,plain,
    ( v1_finset_1(sK11)
    | ~ v2_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(sK10))
    | ~ v2_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r1_lattice3(X0,X4,sK6(X0,X1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f2,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,X2,sK3(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f116,plain,(
    v13_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f122,plain,
    ( ~ r2_hidden(k2_yellow_0(sK9,sK11),sK10)
    | ~ v2_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6858,plain,
    ( m1_subset_1(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6856,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7453,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6858,c_6856])).

cnf(c_15,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_6854,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6848,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7402,plain,
    ( sP0(X0,X1) = iProver_top
    | r1_tarski(sK5(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6854,c_6848])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_6840,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7278,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6840,c_6848])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6857,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7516,plain,
    ( r1_tarski(X0,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7278,c_6857])).

cnf(c_8295,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7516,c_6857])).

cnf(c_9036,plain,
    ( sP0(X0,X1) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | r1_tarski(sK5(X0,X1),u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7402,c_8295])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6849,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_36,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_0,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_294,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_finset_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_0])).

cnf(c_295,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_51,negated_conjecture,
    ( v3_orders_2(sK9) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_775,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_51])).

cnf(c_776,plain,
    ( r2_yellow_0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v5_orders_2(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK9)
    | ~ v2_lattice3(sK9) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_50,negated_conjecture,
    ( v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_49,negated_conjecture,
    ( v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_48,negated_conjecture,
    ( v2_lattice3(sK9) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_47,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_780,plain,
    ( r2_yellow_0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_50,c_49,c_48,c_47])).

cnf(c_6831,plain,
    ( r2_yellow_0(sK9,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_7637,plain,
    ( r2_yellow_0(sK9,X0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK9)) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6849,c_6831])).

cnf(c_19676,plain,
    ( r2_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | sP0(X0,X1) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | v1_finset_1(sK5(X0,X1)) != iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9036,c_7637])).

cnf(c_16,plain,
    ( sP0(X0,X1)
    | v1_finset_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_131,plain,
    ( sP0(X0,X1) = iProver_top
    | v1_finset_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20788,plain,
    ( r1_tarski(X1,sK10) != iProver_top
    | sP0(X0,X1) = iProver_top
    | r2_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19676,c_131])).

cnf(c_20789,plain,
    ( r2_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | sP0(X0,X1) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_20788])).

cnf(c_43,negated_conjecture,
    ( v2_waybel_0(sK10,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
    | r2_hidden(k2_yellow_0(sK9,X0),sK10)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_6841,plain,
    ( k1_xboole_0 = X0
    | v2_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK10)) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_28,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_7,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_308,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_7])).

cnf(c_309,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_308])).

cnf(c_1081,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_49])).

cnf(c_1082,plain,
    ( r1_lattice3(sK9,X0,k2_yellow_0(sK9,X0))
    | ~ r2_yellow_0(sK9,X0)
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_1086,plain,
    ( ~ r2_yellow_0(sK9,X0)
    | r1_lattice3(sK9,X0,k2_yellow_0(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1082,c_47])).

cnf(c_1087,plain,
    ( r1_lattice3(sK9,X0,k2_yellow_0(sK9,X0))
    | ~ r2_yellow_0(sK9,X0) ),
    inference(renaming,[status(thm)],[c_1086])).

cnf(c_6826,plain,
    ( r1_lattice3(sK9,X0,k2_yellow_0(sK9,X0)) = iProver_top
    | r2_yellow_0(sK9,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_14,plain,
    ( ~ r1_lattice3(X0,sK5(X0,X1),X2)
    | sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6855,plain,
    ( r1_lattice3(X0,sK5(X0,X1),X2) != iProver_top
    | sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8134,plain,
    ( r2_yellow_0(sK9,sK5(sK9,X0)) != iProver_top
    | sP0(sK9,X0) = iProver_top
    | m1_subset_1(k2_yellow_0(sK9,sK5(sK9,X0)),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,sK5(sK9,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6826,c_6855])).

cnf(c_1293,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_47])).

cnf(c_1294,plain,
    ( m1_subset_1(k2_yellow_0(sK9,X0),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_6818,plain,
    ( m1_subset_1(k2_yellow_0(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_8582,plain,
    ( r2_yellow_0(sK9,sK5(sK9,X0)) != iProver_top
    | sP0(sK9,X0) = iProver_top
    | r2_hidden(k2_yellow_0(sK9,sK5(sK9,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8134,c_6818])).

cnf(c_8586,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | r2_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | sP0(sK9,sK10) = iProver_top
    | v2_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) != iProver_top
    | v1_finset_1(sK5(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6841,c_8582])).

cnf(c_59,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v2_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_812,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_48])).

cnf(c_813,plain,
    ( ~ l1_orders_2(sK9)
    | ~ v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_71,plain,
    ( ~ l1_orders_2(sK9)
    | ~ v2_lattice3(sK9)
    | ~ v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_815,plain,
    ( ~ v2_struct_0(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_48,c_47,c_71])).

cnf(c_825,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_815])).

cnf(c_826,plain,
    ( sP1(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v4_orders_2(sK9)
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( sP1(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_50,c_47])).

cnf(c_879,plain,
    ( ~ sP0(X0,X1)
    | v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | X2 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_830])).

cnf(c_880,plain,
    ( ~ sP0(sK9,X0)
    | v2_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_7262,plain,
    ( ~ sP0(sK9,sK10)
    | v2_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_7263,plain,
    ( sP0(sK9,sK10) != iProver_top
    | v2_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7262])).

cnf(c_7616,plain,
    ( sP0(X0,sK10)
    | m1_subset_1(sK5(X0,sK10),k1_zfmisc_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7617,plain,
    ( sP0(X0,sK10) = iProver_top
    | m1_subset_1(sK5(X0,sK10),k1_zfmisc_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7616])).

cnf(c_7619,plain,
    ( sP0(sK9,sK10) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7617])).

cnf(c_8036,plain,
    ( sP0(sK9,sK10)
    | v1_finset_1(sK5(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_8037,plain,
    ( sP0(sK9,sK10) = iProver_top
    | v1_finset_1(sK5(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8036])).

cnf(c_8609,plain,
    ( r2_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | sK5(sK9,sK10) = k1_xboole_0
    | v2_waybel_0(sK10,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8586,c_59,c_7263,c_7619,c_8037])).

cnf(c_8610,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | r2_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | v2_waybel_0(sK10,sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_8609])).

cnf(c_20799,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | sP0(sK9,sK10) = iProver_top
    | v2_waybel_0(sK10,sK9) = iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_xboole_0(sK5(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20789,c_8610])).

cnf(c_40,negated_conjecture,
    ( ~ v2_waybel_0(sK10,sK9)
    | k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_65,plain,
    ( k1_xboole_0 != sK11
    | v2_waybel_0(sK10,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_13,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v2_waybel_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_846,plain,
    ( sP0(X0,X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X1)
    | X2 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_830])).

cnf(c_847,plain,
    ( sP0(sK9,X0)
    | ~ v2_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_46,negated_conjecture,
    ( ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1004,plain,
    ( sP0(sK9,X0)
    | ~ v2_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_847,c_46])).

cnf(c_1005,plain,
    ( sP0(sK9,sK10)
    | ~ v2_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1007,plain,
    ( ~ v2_waybel_0(sK10,sK9)
    | sP0(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1005,c_44])).

cnf(c_1008,plain,
    ( sP0(sK9,sK10)
    | ~ v2_waybel_0(sK10,sK9) ),
    inference(renaming,[status(thm)],[c_1007])).

cnf(c_1009,plain,
    ( sP0(sK9,sK10) = iProver_top
    | v2_waybel_0(sK10,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_42,negated_conjecture,
    ( ~ v2_waybel_0(sK10,sK9)
    | v1_finset_1(sK11) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2134,plain,
    ( r2_yellow_0(sK9,X0)
    | ~ v2_waybel_0(sK10,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_780])).

cnf(c_2135,plain,
    ( r2_yellow_0(sK9,sK11)
    | ~ v2_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(sK11) ),
    inference(unflattening,[status(thm)],[c_2134])).

cnf(c_2136,plain,
    ( r2_yellow_0(sK9,sK11) = iProver_top
    | v2_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_2297,plain,
    ( ~ sP0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_finset_1(sK11)
    | sK10 != X0
    | sK9 != sK9 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_880])).

cnf(c_2298,plain,
    ( ~ sP0(sK9,sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_finset_1(sK11) ),
    inference(unflattening,[status(thm)],[c_2297])).

cnf(c_2300,plain,
    ( ~ sP0(sK9,sK10)
    | v1_finset_1(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_44])).

cnf(c_2302,plain,
    ( sP0(sK9,sK10) != iProver_top
    | v1_finset_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2300])).

cnf(c_41,negated_conjecture,
    ( ~ v2_waybel_0(sK10,sK9)
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2311,plain,
    ( ~ sP0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | m1_subset_1(sK11,k1_zfmisc_1(sK10))
    | sK10 != X0
    | sK9 != sK9 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_880])).

cnf(c_2312,plain,
    ( ~ sP0(sK9,sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) ),
    inference(unflattening,[status(thm)],[c_2311])).

cnf(c_2314,plain,
    ( ~ sP0(sK9,sK10)
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2312,c_44])).

cnf(c_2316,plain,
    ( sP0(sK9,sK10) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2314])).

cnf(c_7208,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7209,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7208])).

cnf(c_6828,plain,
    ( sP0(sK9,X0) != iProver_top
    | v2_waybel_0(X0,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_8096,plain,
    ( sP0(sK9,sK10) != iProver_top
    | v2_waybel_0(sK10,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6840,c_6828])).

cnf(c_9438,plain,
    ( r1_tarski(sK11,sK10)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_9439,plain,
    ( r1_tarski(sK11,sK10) = iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9438])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK6(X0,X1,X2),X1)
    | ~ v1_finset_1(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6851,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK6(X0,X1,X2),X1) = iProver_top
    | v1_finset_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( r1_lattice3(X0,X1,sK6(X0,X2,X1))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_finset_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6852,plain,
    ( r1_lattice3(X0,X1,sK6(X0,X2,X1)) = iProver_top
    | sP0(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_7])).

cnf(c_316,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_1057,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_49])).

cnf(c_1058,plain,
    ( ~ r1_lattice3(sK9,X0,X1)
    | r1_orders_2(sK9,X1,k2_yellow_0(sK9,X0))
    | ~ r2_yellow_0(sK9,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_yellow_0(sK9,X0)
    | r1_orders_2(sK9,X1,k2_yellow_0(sK9,X0))
    | ~ r1_lattice3(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_47])).

cnf(c_1063,plain,
    ( ~ r1_lattice3(sK9,X0,X1)
    | r1_orders_2(sK9,X1,k2_yellow_0(sK9,X0))
    | ~ r2_yellow_0(sK9,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_1062])).

cnf(c_6827,plain,
    ( r1_lattice3(sK9,X0,X1) != iProver_top
    | r1_orders_2(sK9,X1,k2_yellow_0(sK9,X0)) = iProver_top
    | r2_yellow_0(sK9,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1302,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_47])).

cnf(c_1303,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,sK9) ),
    inference(unflattening,[status(thm)],[c_1302])).

cnf(c_31,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1319,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1303,c_31])).

cnf(c_6817,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | v13_waybel_0(X2,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_7697,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top
    | v13_waybel_0(sK10,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6840,c_6817])).

cnf(c_45,negated_conjecture,
    ( v13_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1629,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK10 != X2
    | sK9 != sK9 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_1319])).

cnf(c_1630,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ r2_hidden(X0,sK10)
    | r2_hidden(X1,sK10) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_1632,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,X0,X1)
    | ~ r2_hidden(X0,sK10)
    | r2_hidden(X1,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_44])).

cnf(c_1633,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r2_hidden(X0,sK10)
    | r2_hidden(X1,sK10) ),
    inference(renaming,[status(thm)],[c_1632])).

cnf(c_1634,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_7873,plain,
    ( r2_hidden(X1,sK10) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r1_orders_2(sK9,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7697,c_1634])).

cnf(c_7874,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(X1,sK10) = iProver_top ),
    inference(renaming,[status(thm)],[c_7873])).

cnf(c_7884,plain,
    ( r1_orders_2(sK9,X0,k2_yellow_0(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X1),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_6818,c_7874])).

cnf(c_8524,plain,
    ( r1_lattice3(sK9,X0,X1) != iProver_top
    | r2_yellow_0(sK9,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_6827,c_7884])).

cnf(c_6847,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7754,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6840,c_6847])).

cnf(c_8622,plain,
    ( r1_lattice3(sK9,X0,X1) != iProver_top
    | r2_yellow_0(sK9,X0) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X0),sK10) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8524,c_7754])).

cnf(c_8626,plain,
    ( r2_yellow_0(sK9,X0) != iProver_top
    | sP0(sK9,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK6(sK9,X1,X0),sK10) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6852,c_8622])).

cnf(c_10915,plain,
    ( r2_yellow_0(sK9,X0) != iProver_top
    | sP0(sK9,sK10) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK10)) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6851,c_8626])).

cnf(c_39,negated_conjecture,
    ( ~ v2_waybel_0(sK10,sK9)
    | ~ r2_hidden(k2_yellow_0(sK9,sK11),sK10) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_6845,plain,
    ( v2_waybel_0(sK10,sK9) != iProver_top
    | r2_hidden(k2_yellow_0(sK9,sK11),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10951,plain,
    ( r2_yellow_0(sK9,sK11) != iProver_top
    | sP0(sK9,sK10) != iProver_top
    | v2_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) != iProver_top
    | v1_finset_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_10915,c_6845])).

cnf(c_7832,plain,
    ( r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(X0,sK10)
    | ~ r1_tarski(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12416,plain,
    ( ~ r1_tarski(sK10,u1_struct_0(sK9))
    | r1_tarski(sK11,u1_struct_0(sK9))
    | ~ r1_tarski(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_7832])).

cnf(c_12417,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) != iProver_top
    | r1_tarski(sK11,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(sK11,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12416])).

cnf(c_4603,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9544,plain,
    ( X0 != sK5(X1,sK10)
    | X0 = k1_xboole_0
    | k1_xboole_0 != sK5(X1,sK10) ),
    inference(instantiation,[status(thm)],[c_4603])).

cnf(c_12519,plain,
    ( sK5(X0,sK10) != sK5(X0,sK10)
    | sK5(X0,sK10) = k1_xboole_0
    | k1_xboole_0 != sK5(X0,sK10) ),
    inference(instantiation,[status(thm)],[c_9544])).

cnf(c_12520,plain,
    ( sK5(sK9,sK10) != sK5(sK9,sK10)
    | sK5(sK9,sK10) = k1_xboole_0
    | k1_xboole_0 != sK5(sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_12519])).

cnf(c_37,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_14013,plain,
    ( ~ v1_xboole_0(sK5(X0,sK10))
    | k1_xboole_0 = sK5(X0,sK10) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_14014,plain,
    ( k1_xboole_0 = sK5(X0,sK10)
    | v1_xboole_0(sK5(X0,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14013])).

cnf(c_14016,plain,
    ( k1_xboole_0 = sK5(sK9,sK10)
    | v1_xboole_0(sK5(sK9,sK10)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14014])).

cnf(c_14087,plain,
    ( ~ v1_xboole_0(sK11)
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_14089,plain,
    ( k1_xboole_0 = sK11
    | v1_xboole_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14087])).

cnf(c_8879,plain,
    ( r2_yellow_0(sK9,X0) = iProver_top
    | r1_tarski(X0,sK10) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7516,c_7637])).

cnf(c_15646,plain,
    ( r2_yellow_0(sK9,sK5(X0,sK10)) = iProver_top
    | sP0(X0,sK10) = iProver_top
    | v1_finset_1(sK5(X0,sK10)) != iProver_top
    | v1_xboole_0(sK5(X0,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7402,c_8879])).

cnf(c_15731,plain,
    ( r2_yellow_0(sK9,sK5(sK9,sK10)) = iProver_top
    | sP0(sK9,sK10) = iProver_top
    | v1_finset_1(sK5(sK9,sK10)) != iProver_top
    | v1_xboole_0(sK5(sK9,sK10)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15646])).

cnf(c_19909,plain,
    ( ~ r1_tarski(sK11,u1_struct_0(sK9))
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_19910,plain,
    ( r1_tarski(sK11,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19909])).

cnf(c_4602,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_20510,plain,
    ( sK5(X0,sK10) = sK5(X0,sK10) ),
    inference(instantiation,[status(thm)],[c_4602])).

cnf(c_20511,plain,
    ( sK5(sK9,sK10) = sK5(sK9,sK10) ),
    inference(instantiation,[status(thm)],[c_20510])).

cnf(c_20837,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | v2_waybel_0(sK10,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20799,c_59,c_65,c_1009,c_2136,c_2302,c_2316,c_7209,c_8037,c_8096,c_8610,c_9439,c_10951,c_12417,c_12520,c_14016,c_14089,c_15731,c_19910,c_20511])).

cnf(c_20841,plain,
    ( sK5(sK9,sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20837,c_59,c_65,c_1009,c_2136,c_2302,c_2316,c_7209,c_8037,c_8096,c_8610,c_9439,c_10951,c_12417,c_12520,c_14016,c_14089,c_15731,c_19910,c_20511])).

cnf(c_20858,plain,
    ( r1_lattice3(sK9,k1_xboole_0,X0) != iProver_top
    | sP0(sK9,sK10) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_20841,c_6855])).

cnf(c_7195,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ r2_hidden(X0,sK10) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_7196,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7195])).

cnf(c_38,plain,
    ( r1_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1281,plain,
    ( r1_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_47])).

cnf(c_1282,plain,
    ( r1_lattice3(sK9,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_1281])).

cnf(c_6819,plain,
    ( r1_lattice3(sK9,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_7848,plain,
    ( r1_lattice3(sK9,k1_xboole_0,X0) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7754,c_6819])).

cnf(c_21242,plain,
    ( r2_hidden(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20858,c_59,c_65,c_2136,c_2302,c_2316,c_7196,c_7209,c_7848,c_8096,c_9439,c_10951,c_12417,c_14089,c_19910])).

cnf(c_21253,plain,
    ( v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_7453,c_21242])).

cnf(c_57,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21253,c_57])).


%------------------------------------------------------------------------------
