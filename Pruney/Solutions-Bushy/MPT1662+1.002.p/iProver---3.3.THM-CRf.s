%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1662+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  285 (2807 expanded)
%              Number of clauses        :  177 ( 649 expanded)
%              Number of leaves         :   26 ( 711 expanded)
%              Depth                    :   31
%              Number of atoms          : 1332 (31117 expanded)
%              Number of equality atoms :  307 (3531 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK11),X1)
        & k1_xboole_0 != sK11
        & m1_subset_1(sK11,k1_zfmisc_1(X1))
        & v1_finset_1(sK11) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
              ( ~ r2_hidden(k1_yellow_0(X0,X2),sK10)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(sK10))
              & v1_finset_1(X2) )
          | ~ v1_waybel_0(sK10,X0) )
        & ( ! [X3] :
              ( r2_hidden(k1_yellow_0(X0,X3),sK10)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
              | ~ v1_finset_1(X3) )
          | v1_waybel_0(sK10,X0) )
        & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK10,X0)
        & ~ v1_xboole_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
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
                ( ~ r2_hidden(k1_yellow_0(sK9,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,sK9) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(sK9,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,sK9) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK9)))
          & v12_waybel_0(X1,sK9)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK9)
      & v1_lattice3(sK9)
      & v5_orders_2(sK9)
      & v4_orders_2(sK9)
      & v3_orders_2(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( ( ~ r2_hidden(k1_yellow_0(sK9,sK11),sK10)
        & k1_xboole_0 != sK11
        & m1_subset_1(sK11,k1_zfmisc_1(sK10))
        & v1_finset_1(sK11) )
      | ~ v1_waybel_0(sK10,sK9) )
    & ( ! [X3] :
          ( r2_hidden(k1_yellow_0(sK9,X3),sK10)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
          | ~ v1_finset_1(X3) )
      | v1_waybel_0(sK10,sK9) )
    & m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    & v12_waybel_0(sK10,sK9)
    & ~ v1_xboole_0(sK10)
    & l1_orders_2(sK9)
    & v1_lattice3(sK9)
    & v5_orders_2(sK9)
    & v4_orders_2(sK9)
    & v3_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f66,f69,f68,f67])).

fof(f114,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f117,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f70])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,(
    v12_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ( ( ( v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ( ( ( v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( ( v1_waybel_0(X0,X1)
            & ~ v1_xboole_0(X0) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1)
          | v1_xboole_0(X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f39,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f40,f39])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,(
    v1_lattice3(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f111,plain,(
    v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r2_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X4,sK6(X0,X1,X4))
        & r2_hidden(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r2_lattice3(X0,sK5(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r2_lattice3(X0,sK5(X0,X1),X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1))
          & v1_finset_1(sK5(X0,X1)) ) )
      & ( ! [X4] :
            ( ( r2_lattice3(X0,X4,sK6(X0,X1,X4))
              & r2_hidden(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f55,f54])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_lattice3(X0,X4,sK6(X0,X1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(rectify,[],[f8])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK7(X0,X1,X2))
        & r2_lattice3(X0,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK7(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f30,f57])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f112,plain,(
    v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f122,plain,
    ( ~ r2_hidden(k1_yellow_0(sK9,sK11),sK10)
    | ~ v1_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f119,plain,
    ( v1_finset_1(sK11)
    | ~ v1_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(sK10))
    | ~ v1_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f121,plain,
    ( k1_xboole_0 != sK11
    | ~ v1_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v1_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r1_yellow_0(X0,sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,sK8(X0))
            & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK8(X0))
            & ~ v1_xboole_0(sK8(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f61,f62])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    v3_orders_2(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f87,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v1_finset_1(sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f118,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK9,X3),sK10)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK10))
      | ~ v1_finset_1(X3)
      | v1_waybel_0(sK10,sK9) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f124,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r2_lattice3(X0,sK5(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5624,plain,
    ( m1_subset_1(sK4(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5616,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6745,plain,
    ( r2_hidden(sK4(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_5616])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5615,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | v12_waybel_0(X0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_47,negated_conjecture,
    ( l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK2(X1,X0),X0)
    | v12_waybel_0(X0,X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_47])).

cnf(c_1373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(sK2(sK9,X0),X0)
    | v12_waybel_0(X0,sK9) ),
    inference(unflattening,[status(thm)],[c_1372])).

cnf(c_5585,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(sK2(sK9,X0),X0) = iProver_top
    | v12_waybel_0(X0,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_6601,plain,
    ( r1_tarski(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(sK2(sK9,X0),X0) = iProver_top
    | v12_waybel_0(X0,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_5585])).

cnf(c_31,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5613,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7310,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,sK4(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_5613])).

cnf(c_8908,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(X0)),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,sK4(k1_zfmisc_1(X0))),X0) = iProver_top
    | v12_waybel_0(sK4(k1_zfmisc_1(X0)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6601,c_7310])).

cnf(c_17850,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(sK2(sK9,sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))))),sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))))) = iProver_top
    | v12_waybel_0(sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))),sK9) = iProver_top
    | v12_waybel_0(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8908,c_5585])).

cnf(c_17841,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(k1_zfmisc_1(X0))),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,X0) = iProver_top
    | r2_hidden(X1,sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(X0))))) != iProver_top
    | v12_waybel_0(sK4(k1_zfmisc_1(k1_zfmisc_1(X0))),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8908,c_5613])).

cnf(c_18801,plain,
    ( r1_tarski(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK2(sK9,sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))))),u1_struct_0(sK9)) = iProver_top
    | v12_waybel_0(sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))),sK9) = iProver_top
    | v12_waybel_0(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_17850,c_17841])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_5606,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1302,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ v12_waybel_0(X3,X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_47])).

cnf(c_1303,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK9) ),
    inference(unflattening,[status(thm)],[c_1302])).

cnf(c_1319,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | ~ v12_waybel_0(X2,sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1303,c_31])).

cnf(c_5589,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | v12_waybel_0(X2,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_7229,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X0,sK10) = iProver_top
    | v12_waybel_0(sK10,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5606,c_5589])).

cnf(c_45,negated_conjecture,
    ( v12_waybel_0(sK10,sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1629,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X0,X2)
    | sK10 != X2
    | sK9 != sK9 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_1319])).

cnf(c_1630,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ r2_hidden(X1,sK10)
    | r2_hidden(X0,sK10) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_1632,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r1_orders_2(sK9,X0,X1)
    | ~ r2_hidden(X1,sK10)
    | r2_hidden(X0,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_44])).

cnf(c_1633,plain,
    ( ~ r1_orders_2(sK9,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ r2_hidden(X1,sK10)
    | r2_hidden(X0,sK10) ),
    inference(renaming,[status(thm)],[c_1632])).

cnf(c_1634,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X0,sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_7493,plain,
    ( r2_hidden(X0,sK10) = iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r1_orders_2(sK9,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7229,c_1634])).

cnf(c_7494,plain,
    ( r1_orders_2(sK9,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(X0,sK10) = iProver_top ),
    inference(renaming,[status(thm)],[c_7493])).

cnf(c_25128,plain,
    ( r1_orders_2(sK9,sK2(sK9,sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))))),X0) != iProver_top
    | r1_tarski(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK2(sK9,sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))))),sK10) = iProver_top
    | v12_waybel_0(sK2(sK9,sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))),sK9) = iProver_top
    | v12_waybel_0(sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_18801,c_7494])).

cnf(c_59,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v1_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_48,negated_conjecture,
    ( v1_lattice3(sK9) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_812,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_48])).

cnf(c_813,plain,
    ( ~ l1_orders_2(sK9)
    | ~ v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_170,plain,
    ( ~ l1_orders_2(sK9)
    | ~ v1_lattice3(sK9)
    | ~ v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_815,plain,
    ( ~ v2_struct_0(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_48,c_47,c_170])).

cnf(c_825,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_815])).

cnf(c_826,plain,
    ( sP1(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v4_orders_2(sK9)
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_50,negated_conjecture,
    ( v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_830,plain,
    ( sP1(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_50,c_47])).

cnf(c_879,plain,
    ( ~ sP0(X0,X1)
    | v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | X2 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_830])).

cnf(c_880,plain,
    ( ~ sP0(sK9,X0)
    | v1_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_6063,plain,
    ( ~ sP0(sK9,sK10)
    | v1_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_6064,plain,
    ( sP0(sK9,sK10) != iProver_top
    | v1_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6063])).

cnf(c_7314,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5606,c_5613])).

cnf(c_38,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1281,plain,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_47])).

cnf(c_1282,plain,
    ( r2_lattice3(sK9,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_1281])).

cnf(c_5591,plain,
    ( r2_lattice3(sK9,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1282])).

cnf(c_7439,plain,
    ( r2_lattice3(sK9,k1_xboole_0,X0) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_7314,c_5591])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK6(X0,X1,X2),X1)
    | ~ v1_finset_1(X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_5619,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK6(X0,X1,X2),X1) = iProver_top
    | v1_finset_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( r2_lattice3(X0,X1,sK6(X0,X2,X1))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_finset_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5620,plain,
    ( r2_lattice3(X0,X1,sK6(X0,X2,X1)) = iProver_top
    | sP0(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_7,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_7])).

cnf(c_314,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_49,negated_conjecture,
    ( v5_orders_2(sK9) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1057,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_49])).

cnf(c_1058,plain,
    ( ~ r2_lattice3(sK9,X0,X1)
    | r1_orders_2(sK9,k1_yellow_0(sK9,X0),X1)
    | ~ r1_yellow_0(sK9,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1062,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ r1_yellow_0(sK9,X0)
    | r1_orders_2(sK9,k1_yellow_0(sK9,X0),X1)
    | ~ r2_lattice3(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1058,c_47])).

cnf(c_1063,plain,
    ( ~ r2_lattice3(sK9,X0,X1)
    | r1_orders_2(sK9,k1_yellow_0(sK9,X0),X1)
    | ~ r1_yellow_0(sK9,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_1062])).

cnf(c_5599,plain,
    ( r2_lattice3(sK9,X0,X1) != iProver_top
    | r1_orders_2(sK9,k1_yellow_0(sK9,X0),X1) = iProver_top
    | r1_yellow_0(sK9,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1293,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_47])).

cnf(c_1294,plain,
    ( m1_subset_1(k1_yellow_0(sK9,X0),u1_struct_0(sK9)) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_5590,plain,
    ( m1_subset_1(k1_yellow_0(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_7504,plain,
    ( r1_orders_2(sK9,k1_yellow_0(sK9,X0),X1) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_5590,c_7494])).

cnf(c_8207,plain,
    ( r2_lattice3(sK9,X0,X1) != iProver_top
    | r1_yellow_0(sK9,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_5599,c_7504])).

cnf(c_8630,plain,
    ( r2_lattice3(sK9,X0,X1) != iProver_top
    | r1_yellow_0(sK9,X0) != iProver_top
    | r2_hidden(X1,sK10) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8207,c_7314])).

cnf(c_8634,plain,
    ( r1_yellow_0(sK9,X0) != iProver_top
    | sP0(sK9,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK6(sK9,X1,X0),sK10) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5620,c_8630])).

cnf(c_16471,plain,
    ( r1_yellow_0(sK9,X0) != iProver_top
    | sP0(sK9,sK10) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK10)) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5619,c_8634])).

cnf(c_39,negated_conjecture,
    ( ~ v1_waybel_0(sK10,sK9)
    | ~ r2_hidden(k1_yellow_0(sK9,sK11),sK10) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5611,plain,
    ( v1_waybel_0(sK10,sK9) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,sK11),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_16507,plain,
    ( r1_yellow_0(sK9,sK11) != iProver_top
    | sP0(sK9,sK10) != iProver_top
    | v1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) != iProver_top
    | v1_finset_1(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_16471,c_5611])).

cnf(c_42,negated_conjecture,
    ( ~ v1_waybel_0(sK10,sK9)
    | v1_finset_1(sK11) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_63,plain,
    ( v1_waybel_0(sK10,sK9) != iProver_top
    | v1_finset_1(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( ~ v1_waybel_0(sK10,sK9)
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_64,plain,
    ( v1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( ~ v1_waybel_0(sK10,sK9)
    | k1_xboole_0 != sK11 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_65,plain,
    ( k1_xboole_0 != sK11
    | v1_waybel_0(sK10,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v1_waybel_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_846,plain,
    ( sP0(X0,X1)
    | ~ v1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X1)
    | X2 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_830])).

cnf(c_847,plain,
    ( sP0(sK9,X0)
    | ~ v1_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_846])).

cnf(c_46,negated_conjecture,
    ( ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_992,plain,
    ( sP0(sK9,X0)
    | ~ v1_waybel_0(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_847,c_46])).

cnf(c_993,plain,
    ( sP0(sK9,sK10)
    | ~ v1_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_994,plain,
    ( sP0(sK9,sK10) = iProver_top
    | v1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_36,plain,
    ( r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_292,plain,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v1_finset_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_0])).

cnf(c_293,plain,
    ( r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_51,negated_conjecture,
    ( v3_orders_2(sK9) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_775,plain,
    ( r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_finset_1(X1)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_lattice3(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_293,c_51])).

cnf(c_776,plain,
    ( r1_yellow_0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v5_orders_2(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK9)
    | ~ v1_lattice3(sK9) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_780,plain,
    ( r1_yellow_0(sK9,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_50,c_49,c_48,c_47])).

cnf(c_2134,plain,
    ( r1_yellow_0(sK9,X0)
    | ~ v1_waybel_0(sK10,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(X0)
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_780])).

cnf(c_2135,plain,
    ( r1_yellow_0(sK9,sK11)
    | ~ v1_waybel_0(sK10,sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(sK11) ),
    inference(unflattening,[status(thm)],[c_2134])).

cnf(c_2136,plain,
    ( r1_yellow_0(sK9,sK11) = iProver_top
    | v1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v1_xboole_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_30,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6082,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_6083,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) = iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6082])).

cnf(c_5609,plain,
    ( v1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5614,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6214,plain,
    ( r1_tarski(sK11,sK10) = iProver_top
    | v1_waybel_0(sK10,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_5609,c_5614])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6161,plain,
    ( r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(X0,sK10)
    | ~ r1_tarski(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7208,plain,
    ( ~ r1_tarski(sK10,u1_struct_0(sK9))
    | r1_tarski(sK11,u1_struct_0(sK9))
    | ~ r1_tarski(sK11,sK10) ),
    inference(instantiation,[status(thm)],[c_6161])).

cnf(c_7209,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) != iProver_top
    | r1_tarski(sK11,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(sK11,sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7208])).

cnf(c_8287,plain,
    ( ~ r1_tarski(sK11,u1_struct_0(sK9))
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_8288,plain,
    ( r1_tarski(sK11,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK11,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8287])).

cnf(c_37,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_16440,plain,
    ( ~ v1_xboole_0(sK11)
    | k1_xboole_0 = sK11 ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_16441,plain,
    ( k1_xboole_0 = sK11
    | v1_xboole_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16440])).

cnf(c_16552,plain,
    ( v1_waybel_0(sK10,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16507,c_59,c_63,c_64,c_65,c_994,c_2136,c_6083,c_6214,c_7209,c_8288,c_16441])).

cnf(c_13,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5622,plain,
    ( sP0(X0,X1) = iProver_top
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6624,plain,
    ( r1_tarski(sK5(X0,X1),X1) = iProver_top
    | sP0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_5614])).

cnf(c_6215,plain,
    ( r1_tarski(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5606,c_5614])).

cnf(c_5617,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6799,plain,
    ( r1_tarski(X0,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6215,c_5617])).

cnf(c_8090,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK9)) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6799,c_5617])).

cnf(c_10257,plain,
    ( r1_tarski(X0,sK10) != iProver_top
    | r1_tarski(sK5(X1,X0),u1_struct_0(sK9)) = iProver_top
    | sP0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6624,c_8090])).

cnf(c_5603,plain,
    ( r1_yellow_0(sK9,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_7090,plain,
    ( r1_yellow_0(sK9,X0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK9)) != iProver_top
    | v1_finset_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_5603])).

cnf(c_24180,plain,
    ( r1_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | sP0(X0,X1) = iProver_top
    | v1_finset_1(sK5(X0,X1)) != iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10257,c_7090])).

cnf(c_14,plain,
    ( sP0(X0,X1)
    | v1_finset_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_129,plain,
    ( sP0(X0,X1) = iProver_top
    | v1_finset_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24846,plain,
    ( sP0(X0,X1) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | r1_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24180,c_129])).

cnf(c_24847,plain,
    ( r1_yellow_0(sK9,sK5(X0,X1)) = iProver_top
    | r1_tarski(X1,sK10) != iProver_top
    | sP0(X0,X1) = iProver_top
    | v1_xboole_0(sK5(X0,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_24846])).

cnf(c_43,negated_conjecture,
    ( v1_waybel_0(sK10,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK10))
    | r2_hidden(k1_yellow_0(sK9,X0),sK10)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_5607,plain,
    ( k1_xboole_0 = X0
    | v1_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK10)) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,X0),sK10) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_28,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_306,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_7])).

cnf(c_307,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_1081,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_307,c_49])).

cnf(c_1082,plain,
    ( r2_lattice3(sK9,X0,k1_yellow_0(sK9,X0))
    | ~ r1_yellow_0(sK9,X0)
    | ~ l1_orders_2(sK9) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_1086,plain,
    ( ~ r1_yellow_0(sK9,X0)
    | r2_lattice3(sK9,X0,k1_yellow_0(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1082,c_47])).

cnf(c_1087,plain,
    ( r2_lattice3(sK9,X0,k1_yellow_0(sK9,X0))
    | ~ r1_yellow_0(sK9,X0) ),
    inference(renaming,[status(thm)],[c_1086])).

cnf(c_5598,plain,
    ( r2_lattice3(sK9,X0,k1_yellow_0(sK9,X0)) = iProver_top
    | r1_yellow_0(sK9,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,sK5(X0,X1),X2)
    | sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5623,plain,
    ( r2_lattice3(X0,sK5(X0,X1),X2) != iProver_top
    | sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7913,plain,
    ( r1_yellow_0(sK9,sK5(sK9,X0)) != iProver_top
    | sP0(sK9,X0) = iProver_top
    | m1_subset_1(k1_yellow_0(sK9,sK5(sK9,X0)),u1_struct_0(sK9)) != iProver_top
    | r2_hidden(k1_yellow_0(sK9,sK5(sK9,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5598,c_5623])).

cnf(c_8565,plain,
    ( r1_yellow_0(sK9,sK5(sK9,X0)) != iProver_top
    | sP0(sK9,X0) = iProver_top
    | r2_hidden(k1_yellow_0(sK9,sK5(sK9,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7913,c_5590])).

cnf(c_8569,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | r1_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | sP0(sK9,sK10) = iProver_top
    | v1_waybel_0(sK10,sK9) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) != iProver_top
    | v1_finset_1(sK5(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5607,c_8565])).

cnf(c_6146,plain,
    ( sP0(sK9,sK10)
    | v1_finset_1(sK5(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6147,plain,
    ( sP0(sK9,sK10) = iProver_top
    | v1_finset_1(sK5(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6146])).

cnf(c_6145,plain,
    ( sP0(sK9,sK10)
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6149,plain,
    ( sP0(sK9,sK10) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6145])).

cnf(c_8592,plain,
    ( r1_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | sK5(sK9,sK10) = k1_xboole_0
    | v1_waybel_0(sK10,sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8569,c_59,c_6064,c_6147,c_6149])).

cnf(c_8593,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | r1_yellow_0(sK9,sK5(sK9,sK10)) != iProver_top
    | v1_waybel_0(sK10,sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_8592])).

cnf(c_24856,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | r1_tarski(sK10,sK10) != iProver_top
    | sP0(sK9,sK10) = iProver_top
    | v1_waybel_0(sK10,sK9) = iProver_top
    | v1_xboole_0(sK5(sK9,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24847,c_8593])).

cnf(c_6353,plain,
    ( r1_tarski(sK5(sK9,sK10),sK10)
    | ~ m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_6354,plain,
    ( r1_tarski(sK5(sK9,sK10),sK10) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6353])).

cnf(c_6372,plain,
    ( r1_yellow_0(sK9,sK5(sK9,sK10))
    | ~ m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ v1_finset_1(sK5(sK9,sK10))
    | v1_xboole_0(sK5(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_6376,plain,
    ( r1_yellow_0(sK9,sK5(sK9,sK10)) = iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | v1_finset_1(sK5(sK9,sK10)) != iProver_top
    | v1_xboole_0(sK5(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6372])).

cnf(c_6934,plain,
    ( r1_tarski(sK5(sK9,sK10),u1_struct_0(sK9))
    | ~ r1_tarski(sK5(sK9,sK10),sK10)
    | ~ r1_tarski(sK10,u1_struct_0(sK9)) ),
    inference(instantiation,[status(thm)],[c_6161])).

cnf(c_6935,plain,
    ( r1_tarski(sK5(sK9,sK10),u1_struct_0(sK9)) = iProver_top
    | r1_tarski(sK5(sK9,sK10),sK10) != iProver_top
    | r1_tarski(sK10,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6934])).

cnf(c_8872,plain,
    ( ~ r1_tarski(sK5(sK9,sK10),u1_struct_0(sK9))
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_8873,plain,
    ( r1_tarski(sK5(sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(sK5(sK9,sK10),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8872])).

cnf(c_24870,plain,
    ( sK5(sK9,sK10) = k1_xboole_0
    | v1_xboole_0(sK5(sK9,sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24856,c_59,c_63,c_64,c_65,c_994,c_2136,c_6064,c_6083,c_6147,c_6149,c_6214,c_6354,c_6376,c_6935,c_7209,c_8288,c_8569,c_8873,c_16441,c_16507])).

cnf(c_5612,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_24876,plain,
    ( sK5(sK9,sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24870,c_5612])).

cnf(c_24914,plain,
    ( r2_lattice3(sK9,k1_xboole_0,X0) != iProver_top
    | sP0(sK9,sK10) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_24876,c_5623])).

cnf(c_25285,plain,
    ( r2_hidden(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25128,c_59,c_63,c_64,c_65,c_994,c_2136,c_6064,c_6083,c_6214,c_7209,c_7314,c_7439,c_8288,c_16441,c_16507,c_24914])).

cnf(c_25296,plain,
    ( v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_6745,c_25285])).

cnf(c_57,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25296,c_57])).


%------------------------------------------------------------------------------
